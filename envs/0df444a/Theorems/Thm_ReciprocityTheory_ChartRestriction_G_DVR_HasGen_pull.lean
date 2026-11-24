-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.HasGen.pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:15.181442+00:00
-- url     : https://prove2.me/theorems/e97c7010-cfa4-4c83-bc43-4cb636ed27f9
-- title:
--   Has Gen: pull
-- statement:
--   The Has Gen construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L114-L118

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.HasGen.pull {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (h : Z ⟶ Y) :
    HasGen L (Finsupp.mapDomain (fun ψ => h ≫ ψ) F) := by sorry
