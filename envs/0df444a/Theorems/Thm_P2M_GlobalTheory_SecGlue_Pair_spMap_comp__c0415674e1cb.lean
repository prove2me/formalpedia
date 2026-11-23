-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb
-- name    : P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:16.112547+00:00
-- url     : https://prove2.me/theorems/f397cb36-3e24-4bef-8555-3418cff619d9
-- title:
--   P2 M Global Theory Sec Glue Pair sp Map comp  c0415674e1cb: P2 M Global Theory Sec Glue Pair sp Map comp  c0415674e1cb
-- statement:
--   The P2 M Global Theory Sec Glue Pair sp Map comp  c0415674e1cb construction uses the P2 M Global Theory Sec Glue Pair sp Map comp  c0415674e1cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair

theorem P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by sorry

alias «GlobalTheory».«SecGlue».«Pair».«spMap_comp'» := P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb
