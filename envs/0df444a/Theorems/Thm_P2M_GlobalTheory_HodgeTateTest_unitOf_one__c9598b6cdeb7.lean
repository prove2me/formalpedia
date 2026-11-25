-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HodgeTateTest_unitOf_one__c9598b6cdeb7
-- name    : P2M_GlobalTheory_HodgeTateTest_unitOf_one__c9598b6cdeb7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:34.934697+00:00
-- url     : https://prove2.me/theorems/a9a742a5-d4eb-4dc9-8791-3a86c320935a
-- title:
--   P2 M Global Theory Hodge Tate Test unit Of one  c9598b6cdeb7: P2 M Global Theory Hodge Tate Test unit Of one  c9598b6cdeb7
-- statement:
--   The P2 M Global Theory Hodge Tate Test unit Of one  c9598b6cdeb7 construction uses the P2 M Global Theory Hodge Tate Test unit Of one  c9598b6cdeb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean#L24-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]

theorem P2M_GlobalTheory_HodgeTateTest_unitOf_one__c9598b6cdeb7 {R : Type} [CommRing R] [Algebra O R] :
    unitOf (1 : specO O R ⟶ GmO O) = 1 := by sorry

alias «GlobalTheory».«HodgeTateTest».«unitOf_one'» := P2M_GlobalTheory_HodgeTateTest_unitOf_one__c9598b6cdeb7
