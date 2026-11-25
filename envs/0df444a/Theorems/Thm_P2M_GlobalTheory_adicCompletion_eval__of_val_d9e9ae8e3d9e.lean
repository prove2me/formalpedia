-- Prove2me | Theorems.Thm_P2M_GlobalTheory_adicCompletion_eval__of_val_d9e9ae8e3d9e
-- name    : P2M_GlobalTheory_adicCompletion_eval__of_val_d9e9ae8e3d9e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:56.319302+00:00
-- url     : https://prove2.me/theorems/4414d669-7206-41e7-93cd-816568dfc9a1
-- title:
--   P2 M Global Theory adic Completion eval  of val d9e9ae8e3d9e: P2 M Global Theory adic Completion eval  of val d9e9ae8e3d9e
-- statement:
--   The P2 M Global Theory adic Completion eval  of val d9e9ae8e3d9e construction uses the P2 M Global Theory adic Completion eval  of val d9e9ae8e3d9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFinite.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFinite.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem P2M_GlobalTheory_adicCompletion_eval__of_val_d9e9ae8e3d9e {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by sorry

alias «GlobalTheory».«adicCompletion_evalₐ_of_val» := P2M_GlobalTheory_adicCompletion_eval__of_val_d9e9ae8e3d9e
