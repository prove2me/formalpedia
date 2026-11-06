-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_6_2
-- name    : SKWeakPoincare.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:55.005727+00:00
-- url     : https://prove2.me/theorems/a0e5a970-0976-452b-bdfe-a783ab9992fd
-- title:
--   Lemma 6.2 — endpoint comparison: $\|Y^{\omega+h}_T-Y^\omega_T\|_2\le\sqrt T e^{LT}(\|h\|_{H_T}+\sqrt{U(\omega+h)}+\sqrt{U(\omega)})$
-- statement:
--   Let $T,L>0$ and $n\ge2$, let $\mu$ be a full-support law on $\{\pm1\}^n$ with posterior mean $m$, and let $\mathfrak e:[0,T]\times\mathbb R^n\to[0,4n]$ be a jointly Borel cost function such that $m$ has the Lipschitz property with cost functions,
--   $$
--   \|m(y_1)-m(y_2)\|_2\le L\|y_1-y_2\|_2+\sqrt{\mathfrak e(t;y_1)}+\sqrt{\mathfrak e(t;y_2)}\qquad(t\in[0,T]).
--   $$
--   Let $Y^\omega$ be the localization paths, $Y^\omega_t=\omega_t+\int_0^tm(Y^\omega_s)\,ds$, and let $U(\omega)=\int_0^T\mathfrak e(t;Y^\omega_t)\,dt$. Then for every $\omega\in C_0([0,T];\mathbb R^n)$ and $h\in H_T$,
--   $$
--   \|Y^{\omega+h}_T-Y^\omega_T\|_2\le\sqrt T\,e^{LT}\Big(\|h\|_{H_T}+\sqrt{U(\omega+h)}+\sqrt{U(\omega)}\Big).
--   $$
--
--   The lemma controls the endpoints of the two nearby paths produced by Gaussian isoperimetry in the proof of Lemma 6.1.
--
--   **Formalization Note** The factor $\sqrt T\,e^{LT}$ multiplies all three terms, as on the printed page and in the last line of the proof (p. 38); the PDF text layer drops the parentheses. The localization map $Y$ is a hypothesis that it solves (8) for every continuous path.
--
--   Differences from the source:
--   - encoding: the setting 'defined above' (Lemma 6.1): T, L > 0, n ≥ 2, μ of full support, 𝔢 a cost function with the Lipschitz property for m → explicit hypotheses 0 < T, 0 < L, 2 ≤ n, IsFullSupportLaw μ, IsCostFn T n e, HasLipCost T L (postMean μ) e; reason: the lemma refers to the objects of Lemma 6.1
--   - encoding: the localization paths Y^ω of eq. (8) for ω ∈ C₀ → a map Y on C([0,T];ℝⁿ) with IsLocPath (postMean μ) ω (Y ω) for every path ω; reason: m is globally n-Lipschitz, so (8) has a unique solution for every continuous ω; Y is that solution map
--   - encoding: h ∈ H_T with ‖h‖_{H_T} → IsCMShift g h with cmNorm T g; reason: h ∈ H_T iff h = ∫₀ˢ g with g ∈ L², ‖h‖_{H_T} = ‖g‖_{L²}
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 6.2, p.37 (proof pp.37–38), in the setting of Lemma 6.1, p.37

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKWeakPoincare_postMean
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKWeakPoincare_IsCostFn

open OAI.CriticalSK MeasureTheory

namespace SKWeakPoincare

/-- **Lemma 6.2 (endpoint comparison).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.2, p. 37 (proof pp. 37–38), in the setting of Lemma 6.1, p. 37.

Let `T, L > 0`, `n ≥ 2`, `μ` a full-support distribution on `{±1}^n` with posterior mean `m`, and
`𝔢 : [0, T] × ℝ^n → [0, 4n]` jointly Borel with the Lipschitz property with cost functions
`‖m(y₁) − m(y₂)‖₂ ≤ L‖y₁ − y₂‖₂ + √𝔢(t; y₁) + √𝔢(t; y₂)`. Let `Y^ω` be the localization paths
(`Y^ω_t = ω_t + ∫₀ᵗ m(Y^ω_s) ds`) and `U(ω) = ∫₀ᵀ 𝔢(t; Y^ω_t) dt`. Then for every
`ω ∈ C₀([0, T]; ℝ^n)` and `h ∈ H_T`,
`‖Y^{ω+h}_T − Y^ω_T‖₂ ≤ √T exp(LT) (‖h‖_{H_T} + √U(ω + h) + √U(ω))`.

**Formalization Note.** `√T exp(LT)` multiplies all three terms, as on the printed page and in the
last line of the proof (p. 38); the PDF text layer drops the parentheses. The localization map is any
`Y` with `IsLocPath (postMean μ) ω (Y ω)` for every path `ω` (for each continuous `ω` the solution
exists and is unique, since `m` is globally `n`-Lipschitz, p. 16–17). `h ∈ H_T` is `IsCMShift g h`,
`‖h‖_{H_T} = cmNorm T g`. -/
theorem lemma_6_2 (T L : ℝ) (hT : 0 < T) (hL : 0 < L) (n : ℕ) (hn : 2 ≤ n)
    (μ : Spin n → ℝ) (hμ : IsFullSupportLaw μ) (e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (he : IsCostFn T n e) (hlip : HasLipCost T L (postMean μ) e)
    (Y : PathSpace T n → PathSpace T n) (hY : ∀ ω, IsLocPath (postMean μ) ω (Y ω)) :
    ∀ (ω h : PathSpace T n) (g : ℝ → EuclideanSpace ℝ (Fin n)), pathExt ω 0 = 0 → IsCMShift g h →
      ‖pathExt (Y (ω + h)) T - pathExt (Y ω) T‖ ≤
        Real.sqrt T * Real.exp (L * T) *
          (cmNorm T g + Real.sqrt (pathCost T e (Y (ω + h))) + Real.sqrt (pathCost T e (Y ω))) := by sorry

end SKWeakPoincare
