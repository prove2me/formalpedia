-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PDivGroup_conv_eq_one_of_forall_pairing__b1a5d38aac2b
-- name    : P2M_GlobalTheory_PDivGroup_conv_eq_one_of_forall_pairing__b1a5d38aac2b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:23.453253+00:00
-- url     : https://prove2.me/theorems/b2ebd9df-2c79-499b-bd7b-8f4841b6116d
-- title:
--   P2 M Global Theory PDiv Group conv eq one of forall pairing  b1a5d38aac2b: P2 M Global Theory PDiv Group conv eq one of forall pairing  b1a5d38aac2b
-- statement:
--   The P2 M Global Theory PDiv Group conv eq one of forall pairing  b1a5d38aac2b construction uses the P2 M Global Theory PDiv Group conv eq one of forall pairing  b1a5d38aac2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L394-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L394-L402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]

theorem P2M_GlobalTheory_PDivGroup_conv_eq_one_of_forall_pairing__b1a5d38aac2b (t : G.Tate) (n : ℕ)
    (h : ∀ χ : G.dual.Tate, muRoot (pairing G O t χ) n = 1) : t.conv n = 1 := by sorry

alias «GlobalTheory».«PDivGroup».«conv_eq_one_of_forall_pairing'» := P2M_GlobalTheory_PDivGroup_conv_eq_one_of_forall_pairing__b1a5d38aac2b
