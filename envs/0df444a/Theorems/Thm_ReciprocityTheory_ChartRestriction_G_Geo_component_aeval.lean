-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_component_aeval
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.component_aeval
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:57.345818+00:00
-- url     : https://prove2.me/theorems/2cde65da-f4d3-4e0f-895d-8679028917a6
-- title:
--   Geo: component aeval
-- statement:
--   The Geo construction uses the component aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L81-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.component_aeval {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℚ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by sorry
