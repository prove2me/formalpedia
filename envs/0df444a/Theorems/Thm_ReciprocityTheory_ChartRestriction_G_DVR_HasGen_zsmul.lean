-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zsmul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.HasGen.zsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:04.820214+00:00
-- url     : https://prove2.me/theorems/37374710-df5f-4cfd-80cb-0349b06adbf7
-- title:
--   Has Gen: zsmul
-- statement:
--   The Has Gen construction uses the zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L110-L112

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.HasGen.zsmul {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : ∀ n : ℤ, HasGen L (n • F)
  := by sorry
