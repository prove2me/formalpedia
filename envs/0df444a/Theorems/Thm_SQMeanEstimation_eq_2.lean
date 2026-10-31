-- Prove2me | Theorems.Thm_SQMeanEstimation_eq_2
-- name    : SQMeanEstimation.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:02.424779+00:00
-- url     : https://prove2.me/theorems/8fa7d9da-a85a-4022-ab65-e1bfda64d0d5
-- title:
--   Eq. (2) — $\|u\|_1=2^j\|\mathbf E[R_j(w^+)]\|_1\le2^{(j+1)q-1}$
-- statement:
--   Let $q\in(1,2)$, $j\in\mathbb N$, and let $\mathbf w$ be a random vector in $\mathbb R^d$ with $\|\mathbf w\|_q\le1$ almost surely. With $u=2^j\,\mathbf E[R_j(\mathbf w^+)]$,
--   $$
--   \|u\|_1=2^j\,\big\|\mathbf E[R_j(\mathbf w^+)]\big\|_1\le 2^j\,(2^{-j-1})^{1-q}=2^{(j+1)q-1}.
--   $$
--
--   This bounds the total mass of the rescaled level-$j$ mean, which feeds eqs. (3) and (4).
--
--   Differences from the source:
--   - encoding: w a random variable supported on B_q^d; E → μ a Borel probability measure on Fin d → ℝ with lqNorm q w ≤ 1 μ-a.s.; Bochner integral; reason: the distribution of the random variable; the integrand is measurable and bounded, hence integrable
--   - encoding: ‖u‖₁ = 2ʲ·‖w̄^{+,j}‖₁ = 2ʲ·‖E[Rⱼ(w⁺)]‖₁ → ∑ i, |2 ^ j * (∫ w, Rⱼ(w⁺) ∂μ) i|; reason: the two equalities are the definitions of u and w̄^{+,j}; the Lean term is their common value
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, eq. (2), p.18

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_posPart
import Definitions.Def_SQMeanEstimation_ringPart

open MeasureTheory

namespace SQMeanEstimation

/-- **Eq. (2) — ℓ₁ norm of the rescaled mean of a ring.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, eq. (2), p.18:
"‖u‖₁ = 2ʲ · ‖w̄^{+,j}‖₁ = 2ʲ · ‖E[Rⱼ(w⁺)]‖₁ ≤ 2ʲ · (2^{−j−1})^{1−q} = 2^{(j+1)q−1}", with
`u = 2ʲ · w̄^{+,j}` and `w̄^{+,j} = E[Rⱼ(w⁺)]` (p.17), `w` a random variable supported on `Bᵈ_q`.

For `q ∈ (1, 2)`, `j ∈ ℕ` and every Borel probability measure `μ` on ℝᵈ with `‖w‖_q ≤ 1`
`μ`-a.s.: `Σᵢ |2ʲ·(E_μ[Rⱼ(w⁺)])ᵢ| ≤ 2ʲ·(2^{−j−1})^{1−q}`, and `2ʲ·(2^{−j−1})^{1−q} = 2^{(j+1)q−1}`.

**Formalization Note.** The expectation is the Bochner integral of the vector-valued map
`w ↦ Rⱼ(w⁺)` (measurable and bounded, hence integrable). The two equalities before "≤" on the
page are the definitions of `u` and `w̄^{+,j}`. -/
theorem eq_2 {d : ℕ} (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (j : ℕ)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ w ∂μ, lqNorm q w ≤ 1) :
    ∑ i, |(2 : ℝ) ^ j * (∫ w, ringPart j (posPart w) ∂μ) i| ≤
        (2 : ℝ) ^ j * ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) ∧
      (2 : ℝ) ^ j * ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) = (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)
    := by sorry

end SQMeanEstimation
