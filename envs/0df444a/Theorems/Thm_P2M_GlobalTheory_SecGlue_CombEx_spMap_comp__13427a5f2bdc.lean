-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SecGlue_CombEx_spMap_comp__13427a5f2bdc
-- name    : P2M_GlobalTheory_SecGlue_CombEx_spMap_comp__13427a5f2bdc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:59.768245+00:00
-- url     : https://prove2.me/theorems/ec0c758e-3f69-4212-9b26-80949a84e30a
-- title:
--   P2 M Global Theory Sec Glue Comb Ex sp Map comp  13427a5f2bdc: P2 M Global Theory Sec Glue Comb Ex sp Map comp  13427a5f2bdc
-- statement:
--   The P2 M Global Theory Sec Glue Comb Ex sp Map comp  13427a5f2bdc construction uses the P2 M Global Theory Sec Glue Comb Ex sp Map comp  13427a5f2bdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L30-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx

theorem P2M_GlobalTheory_SecGlue_CombEx_spMap_comp__13427a5f2bdc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by sorry

alias «GlobalTheory».«SecGlue».«CombEx».«spMap_comp'» := P2M_GlobalTheory_SecGlue_CombEx_spMap_comp__13427a5f2bdc
