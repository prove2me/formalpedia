-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mul_mem_identityComponent_of_rational__c555fc7d5940
-- name    : P2M_GlobalTheory_T_mul_mem_identityComponent_of_rational__c555fc7d5940
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:38.322634+00:00
-- url     : https://prove2.me/theorems/d93457fc-934d-497d-8836-8ee18589e882
-- title:
--   P2 M Global Theory T mul mem identity Component of rational  c555fc7d5940: P2 M Global Theory T mul mem identity Component of rational  c555fc7d5940
-- statement:
--   The P2 M Global Theory T mul mem identity Component of rational  c555fc7d5940 construction uses the P2 M Global Theory T mul mem identity Component of rational  c555fc7d5940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulMemIdentityComponentOfRationalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulMemIdentityComponentOfRationalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRationalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mul_mem_identityComponent_of_rational__c555fc7d5940 : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by sorry

alias «GlobalTheory».«T».«mul_mem_identityComponent_of_rational'» := P2M_GlobalTheory_T_mul_mem_identityComponent_of_rational__c555fc7d5940
