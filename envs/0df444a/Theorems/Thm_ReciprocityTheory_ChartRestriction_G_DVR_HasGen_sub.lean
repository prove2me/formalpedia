-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_sub
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.HasGen.sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:17.405242+00:00
-- url     : https://prove2.me/theorems/cec84055-6520-4ab3-a91b-dbe0ddfd973b
-- title:
--   Has Gen: sub
-- statement:
--   The Has Gen construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L103-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}

theorem ReciprocityTheory.ChartRestriction.G.DVR.HasGen.sub {F G : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (hG : HasGen L G) : HasGen L (F - G) := by sorry
