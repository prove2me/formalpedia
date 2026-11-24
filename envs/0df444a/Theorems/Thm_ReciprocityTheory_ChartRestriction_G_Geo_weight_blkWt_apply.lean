-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blkWt_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.weight_blkWt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:44.375655+00:00
-- url     : https://prove2.me/theorems/048e3cbe-037a-45f3-b0a6-d2fa40fa5101
-- title:
--   Geo: weight blk Wt apply
-- statement:
--   The Geo construction uses the weight blk Wt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L18-L29

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.weight_blkWt_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkWt (ι := ι)) m k = ∑ i, m ⟨k, i⟩ := by sorry
