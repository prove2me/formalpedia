-- Prove2me | Theorems.Thm_SigRoute_lemma_1
-- name    : SigRoute.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:38:51.585205+00:00
-- url     : https://prove2.me/theorems/8a06d4ec-bb47-40b5-bc4c-13fa7bc8f3ae
-- title:
--   Lemma 1 — moment generating function tail bound $\mathbb P[S\ge\tau]\le e^{-\lambda\tau}\Lambda^N$
-- statement:
--   Let $(\mathcal F_j)$ be a filtration and $Y_1,\dots,Y_N\ge0$ random variables with $Y_j$ being $\mathcal F_j$-measurable. Let $\lambda>0$ and $\Lambda\ge1$ satisfy
--
--   $$
--   \mathbb E\bigl[e^{\lambda Y_j}\mid\mathcal F_{j-1}\bigr]\le\Lambda\quad\text{almost surely, for all } j.
--   $$
--
--   Then for $S=\sum_jY_j$ and every $\tau\in\mathbb R$,
--
--   $$
--   \mathbb P[S\ge\tau]\le e^{-\lambda\tau}\Lambda^N .
--   $$
--
--   No independence is assumed: the $Y_j$ may depend on the whole past. This is the adaptive Chernoff bound behind Theorem 14.
--
--   **Formalization Note** Rounds are 0-based: $Y_j$ ($j<N$) is `F (j+1)`-measurable and is conditioned on `F j`.
--
--   Differences from the source:
--   - generalization: $\mathcal F_j$ the σ-algebra of the first $j$ rounds of a routed session → an arbitrary filtration of an arbitrary probability space; reason: the session's filtration is an instance
--   - encoding: rounds $j=1,\dots,N$ conditioned on $\mathcal F_{j-1}$, answers $a_j\in\{0,1\}$ → 0-based rounds $j<N$ conditioned on `F j`, answers in `Bool`; reason: relabelling; same instances
--   - encoding: $\mathbb E[e^{\lambda Y_j}\mid\mathcal F_{j-1}]\le\Lambda$ (extended-valued conditional expectation) → the same, plus `Integrable (fun ω => exp (λ * Y j ω)) μ`; reason: Mathlib's conditional expectation of a non-integrable function is 0; in the paper the hypothesis forces $\mathbb E e^{\lambda Y_j}\le\Lambda<\infty$, so only Lean's junk case is excluded
--   - encoding: $\mathbb P[S\ge\tau]$ and conditional probabilities $\mathbb P[E\mid\mathcal F]$ almost surely → `μ.real {ω | τ ≤ creditSum …}` and `condProb` (Mathlib `condExp` of the indicator), with `∀ᵐ`; reason: Lean convention; the events are measurable, so these are the paper's quantities
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 1, p.4

import Mathlib

namespace SigRoute

open MeasureTheory

/-- Lemma 1 (Moment generating function tail bound) (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 1, p.4). Let `Y_1, …, Y_N ≥ 0` be
random variables with `Y_j` being `F_j`-measurable, and let `λ > 0` and `Λ ≥ 1` satisfy
`E[e^{λY_j} | F_{j−1}] ≤ Λ` for all `j`. Then for `S = ∑_j Y_j` and every `τ ∈ ℝ`,
`P[S ≥ τ] ≤ e^{−λτ} Λ^N`.

**Formalization Note** Rounds are 0-based: `Y j` (`j < N`) is `F (j+1)`-measurable and is conditioned on
`F j`. The filtration is an arbitrary filtration of an arbitrary probability space. The hypothesis
`Integrable (e^{λ Y_j})` is added because Mathlib's conditional expectation of a non-integrable function
is `0`, which would make the moment hypothesis vacuous; in the paper the hypothesis forces
`E e^{λY_j} ≤ Λ < ∞`. -/
theorem lemma_1 {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m) (N : ℕ) (Y : ℕ → Ω → ℝ)
    (hY_nonneg : ∀ j < N, ∀ ω, 0 ≤ Y j ω)
    (hY_meas : ∀ j < N, Measurable[F (j + 1)] (Y j))
    (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : 1 ≤ Λ)
    (hint : ∀ j < N, Integrable (fun ω => Real.exp (lam * Y j ω)) μ)
    (hmgf : ∀ j < N, condExp (F j) μ (fun ω => Real.exp (lam * Y j ω)) ≤ᵐ[μ] fun _ => Λ)
    (τ : ℝ) :
    μ.real {ω | τ ≤ ∑ j ∈ Finset.range N, Y j ω} ≤ Real.exp (-lam * τ) * Λ ^ N := by sorry

end SigRoute
