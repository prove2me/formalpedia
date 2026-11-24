-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_neg
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.HasGen.neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:26.251054+00:00
-- url     : https://prove2.me/theorems/616da94a-ee6c-49ed-8f07-5f9a1aa568b2
-- title:
--   Has Gen: neg
-- statement:
--   The Has Gen construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L86-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L86-L101

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.HasGen.neg {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : HasGen L (-F) := by sorry
