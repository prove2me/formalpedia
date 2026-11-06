-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_2_1
-- name    : SKWeakPoincare.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:59.820996+00:00
-- url     : https://prove2.me/theorems/9c980be9-79b2-44da-b391-e0747572c8a5
-- title:
--   Lemma 2.1 — Lipschitz property of the posterior mean with cost functions
-- statement:
--   Fix $0<\beta_0<\beta_1<1$ and $T>0$. There is a constant $L$ such that, for every $n$ and every $\beta\in[\beta_0,\beta_1]$, there is a jointly Borel function $\mathfrak e_{n,\beta}:\mathbb R^{n\times n}_{\mathrm{sym},0}\times[0,T]\times\mathbb R^n\to[0,4n]$ with the following properties.
--
--   1. For every $A$, every $t\in[0,T]$ and all $y_1,y_2\in\mathbb R^n$,
--   $$
--   \|m(A,y_1)-m(A,y_2)\|_2\le L\|y_1-y_2\|_2+\sqrt{\mathfrak e_{n,\beta}(A,t;y_1)}+\sqrt{\mathfrak e_{n,\beta}(A,t;y_2)} .
--   $$
--   2. For every $R>0$ there are $C_R,n_R>0$ such that for every $n\ge n_R$ and every $\beta\in[\beta_0,\beta_1]$,
--   $$
--   P^{\mathrm{aug}}_{0,n,\beta}\Big[\int_0^T\mathfrak e_{n,\beta}(A,t;Y_t)\,dt>C_R\log n\Big]\le n^{-R},\qquad P^{\mathrm{aug}}_{0,n,\beta}\big[\mathfrak e_{n,\beta}(A,T;Y_T)>C_R\log n\big]\le n^{-R}.
--   $$
--
--   Here $m(A,y)$ is the mean of the SK Gibbs law at inverse temperature $\beta$ with external field $y$, and $P^{\mathrm{aug}}_{0,n,\beta}$ draws $A\sim P_{0,n}$, then $X\sim\mu_{\beta,A}$, and sets $Y_t=tX+B_t$ for an independent Brownian motion. The lemma replaces a global Lipschitz bound on the posterior mean by one that holds up to a cost which is $O(\log n)$ along typical localization paths.
--
--   **Formalization Note** The family $\mathfrak e$ (one function for each $n$ and $\beta$) is chosen before $R$. $P^{\mathrm{aug}}_{0,n,\beta}$ is any probability space carrying `IsAugOriginal`.
--
--   Differences from the source:
--   - encoding: 𝔢_{n,β} jointly Borel on ℝ^{n×n}_{sym,0} × [0,T] × ℝⁿ with values in [0,4n] → e n β Borel on Disorder n × ℝ × ℝⁿ, with values in [0,4n] for t ∈ [0,T]; reason: Disorder n is ℝ^{n×n}_{sym,0}; every Borel function on [0,T] extends Borel-measurably to ℝ
--   - encoding: (i) for every A, t → for every W and every t ∈ [0,T]; reason: [0,T] is the domain of 𝔢_{n,β}
--   - encoding: sup over β ∈ [β₀,β₁] of each probability is ≤ n^{−R} → for every β ∈ [β₀,β₁] each probability is ≤ n^{−R}; reason: a supremum is ≤ c iff every term is
--   - encoding: the joint law P^aug_{0,n,β} of (X, A, d, Y) → every probability space (Ω : Type) with IsAugOriginal β P Wr σ B and Y_t = augField σ B t; reason: the events depend only on the joint law of (A, X, B); the diagonal d enters no event; one such space realizes the law
--   - encoding: the time integral ∫₀ᵀ 𝔢_{n,β}(A, t; Y_t) dt → the interval Bochner integral of t ↦ e n β (Wr ω) t (Y_t ω); reason: e is bounded and Borel on [0,T] and the Brownian paths are continuous almost surely, so the integrand is integrable off a P-null set, which does not change the probability
--   - encoding: C_R, n_R > 0 → C : ℝ with 0 < C and nR : ℕ with 0 < nR; reason: n is a natural number
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 2.1, p.8

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKWeakPoincare_postMean
import Definitions.Def_SKWeakPoincare_IsCostFn
import Definitions.Def_SKWeakPoincare_IsAugOriginal

open OAI.CriticalSK MeasureTheory
open scoped NNReal

namespace SKWeakPoincare

/-- **Lemma 2.1 (Lipschitz property with cost functions).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 2.1, p. 8.

Fix `0 < β₀ < β₁ < 1` and `T > 0`. There is a constant `L` such that, for every `n` and every
`β ∈ [β₀, β₁]`, there is a jointly Borel `𝔢_{n,β} : ℝ^{n×n}_{sym,0} × [0, T] × ℝ^n → [0, 4n]` with
(i) `‖m(A, y₁) − m(A, y₂)‖₂ ≤ L‖y₁ − y₂‖₂ + √𝔢_{n,β}(A, t; y₁) + √𝔢_{n,β}(A, t; y₂)` for every `A`,
`t` and `y₁, y₂`; and (ii) for every `R > 0` there are `C_R, n_R > 0` such that for every `n ≥ n_R`,
`sup_{β∈[β₀,β₁]} P^aug_{0,n,β}[∫₀ᵀ 𝔢_{n,β}(A, t; Y_t) dt > C_R log n] ≤ n^{−R}` and
`sup_{β∈[β₀,β₁]} P^aug_{0,n,β}[𝔢_{n,β}(A, T; Y_T) > C_R log n] ≤ n^{−R}`.

**Formalization Note.** `A ∈ ℝ^{n×n}_{sym,0}` is `W : Disorder n`; `m(A, y) = postMean (gibbs (β • W)) y`.
The family `𝔢` is chosen before `R`. `𝔢_{n,β}` is Borel on `Disorder n × ℝ × ℝ^n` (a Borel extension
off `t ∈ [0, T]`), with values in `[0, 4n]` for `t ∈ [0, T]`. `P^aug_{0,n,β}` is any probability space
carrying `IsAugOriginal β P Wr σ B`, with `Y_t = augField σ B t`; the supremum over `β` is "for every
`β`". -/
theorem lemma_2_1 (β₀ β₁ T : ℝ) (h0 : 0 < β₀) (h01 : β₀ < β₁) (h1 : β₁ < 1) (hT : 0 < T) :
    ∃ (L : ℝ) (e : (n : ℕ) → ℝ → Disorder n → ℝ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ n : ℕ, ∀ β ∈ Set.Icc β₀ β₁,
        Measurable (fun p : Disorder n × ℝ × EuclideanSpace ℝ (Fin n) => e n β p.1 p.2.1 p.2.2) ∧
        (∀ W : Disorder n, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y,
          0 ≤ e n β W t y ∧ e n β W t y ≤ 4 * (n : ℝ)) ∧
        (∀ W : Disorder n, HasLipCost T L (postMean (gibbs (β • W))) (e n β W))) ∧
      ∀ R : ℝ, 0 < R → ∃ (C : ℝ) (nR : ℕ), 0 < C ∧ 0 < nR ∧ ∀ n : ℕ, nR ≤ n →
        ∀ β ∈ Set.Icc β₀ β₁, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Wr : Ω → Disorder n) (σ : Ω → Spin n) (B : ℝ≥0 → Ω → (Fin n → ℝ)),
          IsAugOriginal β P Wr σ B →
          P {ω | C * Real.log n <
              ∫ t in (0 : ℝ)..T, e n β (Wr ω) t (WithLp.toLp 2 (augField σ B t ω))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-R)) ∧
          P {ω | C * Real.log n < e n β (Wr ω) T (WithLp.toLp 2 (augField σ B T ω))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-R)) := by sorry

end SKWeakPoincare
