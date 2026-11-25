-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isSemisimpleRepresentation_tprod_of_isIrreducible__c2ce9d4f8439
-- name    : P2M_GlobalTheory_T_isSemisimpleRepresentation_tprod_of_isIrreducible__c2ce9d4f8439
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:21.745493+00:00
-- url     : https://prove2.me/theorems/747912e4-f114-509d-8892-285ce1b4cf7a
-- title:
--   P2 M Global Theory T is Semisimple Representation tprod of is Irreducible  c2ce9d4f8439: P2 M Global Theory T is Semisimple Representation tprod of is Irreducible  c2ce9d4f8439
-- statement:
--   The P2 M Global Theory T is Semisimple Representation tprod of is Irreducible  c2ce9d4f8439 construction uses the P2 M Global Theory T is Semisimple Representation tprod of is Irreducible  c2ce9d4f8439 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isSemisimpleRepresentation_tprod_of_isIrreducible__c2ce9d4f8439 : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by sorry

alias «GlobalTheory».«T».«isSemisimpleRepresentation_tprod_of_isIrreducible'» := P2M_GlobalTheory_T_isSemisimpleRepresentation_tprod_of_isIrreducible__c2ce9d4f8439
