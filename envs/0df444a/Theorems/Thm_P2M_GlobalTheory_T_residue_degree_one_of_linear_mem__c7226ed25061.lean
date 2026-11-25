-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_residue_degree_one_of_linear_mem__c7226ed25061
-- name    : P2M_GlobalTheory_T_residue_degree_one_of_linear_mem__c7226ed25061
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:06.561213+00:00
-- url     : https://prove2.me/theorems/432d463b-0a1e-42aa-997d-351a51770412
-- title:
--   P2 M Global Theory T residue degree one of linear mem  c7226ed25061: P2 M Global Theory T residue degree one of linear mem  c7226ed25061
-- statement:
--   The P2 M Global Theory T residue degree one of linear mem  c7226ed25061 construction uses the P2 M Global Theory T residue degree one of linear mem  c7226ed25061 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ResidueDegreeOneOfLinearMemStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ResidueDegreeOneOfLinearMemStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ResidueDegreeOneOfLinearMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ResidueDegreeOneOfLinearMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_residue_degree_one_of_linear_mem__c7226ed25061 : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by sorry

alias «GlobalTheory».«T».«residue_degree_one_of_linear_mem'» := P2M_GlobalTheory_T_residue_degree_one_of_linear_mem__c7226ed25061
