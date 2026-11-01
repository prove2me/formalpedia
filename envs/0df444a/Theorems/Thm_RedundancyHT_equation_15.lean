-- Prove2me | Theorems.Thm_RedundancyHT_equation_15
-- name    : RedundancyHT.equation_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:59.228641+00:00
-- url     : https://prove2.me/theorems/8896c7b5-f3dd-43c7-871d-a4cb5d3ae05b
-- title:
--   (15), p.18: the transform of the limit vector
-- statement:
--   Let $E$ be exponential with rate one and $X=\bigl(E\,(p_S/p_{\mathcal T^*})_{S\in\mathcal T^*},(0)_{S\notin\mathcal T^*}\bigr)$. For $t\ge0$,
--   $$\mathbb E\Bigl[\prod_{S\in\mathcal T^*}\exp\Bigl(-t_S\frac{p_S}{p_{\mathcal T^*}}E\Bigr)\Bigr]=\mathbb E\Bigl[\exp\Bigl(-\Bigl(\sum_{S\in\mathcal T^*}\frac{p_S}{p_{\mathcal T^*}}t_S\Bigr)E\Bigr)\Bigr]=\Bigl(1+\sum_{S\in\mathcal T^*}\frac{p_S}{p_{\mathcal T^*}}t_S\Bigr)^{-1}.$$
--   The law of $X$ is a probability measure concentrated on the non-negative orthant.
--
--   This identifies the right-hand side of (14) as the transform of the claimed limit.
--
--   Differences from the source:
--   - generalization: 𝒯* the critical subset → any non-empty set of job types; reason: the computation does not use criticality, and the critical subset is non-empty
--   - encoding: ∏_{S∈𝒯*} exp(−t_S (p_S/p_𝒯*) Exp(1)) → laplace, the exponential of the sum over all coordinates of X; reason: coordinates off 𝒯 vanish and the exponential of a sum is the product
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (15), p.18

import Definitions.Def_RedundancyHT_limitLaw
import Definitions.Def_RedundancyHT_laplace

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The transform (15) of the limit vector `X`** (arXiv:2005.14566v5, p.18). `X` is a probability
law on the non-negative orthant, and at `t ≥ 0` the two equalities of (15) hold.

**Formalization Note.** `laplace` writes `∏_S exp(-t_S X_S)` as `exp(-Σ_S t_S X_S)`. Coordinates off
`𝒯` vanish, so the product over all types is the product over `𝒯` on the page. -/
theorem equation_15 {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) (hT : T.Nonempty) :
    MeasureTheory.IsProbabilityMeasure (limitLaw D T) ∧
      (∀ᵐ x ∂(limitLaw D T), ∀ i, 0 ≤ x i) ∧
      ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
        laplace (limitLaw D T) t =
            ∫ y, Real.exp (-(∑ i ∈ T, pOf D i / pSet D T * t i) * y)
              ∂(ProbabilityTheory.expMeasure 1) ∧
        ∫ y, Real.exp (-(∑ i ∈ T, pOf D i / pSet D T * t i) * y)
              ∂(ProbabilityTheory.expMeasure 1) =
          (1 + ∑ i ∈ T, pOf D i / pSet D T * t i)⁻¹ := by sorry

end RedundancyHT
