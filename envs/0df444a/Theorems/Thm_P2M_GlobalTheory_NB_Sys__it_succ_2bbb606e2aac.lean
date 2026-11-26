-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NB_Sys__it_succ_2bbb606e2aac
-- name    : P2M_GlobalTheory_NB_Sys__it_succ_2bbb606e2aac
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:21.38946+00:00
-- url     : https://prove2.me/theorems/366d964c-e721-48f8-90e1-dec789d42204
-- title:
--   P2 M Global Theory NB Sys  it succ 2bbb606e2aac: P2 M Global Theory NB Sys  it succ 2bbb606e2aac
-- statement:
--   The P2 M Global Theory NB Sys  it succ 2bbb606e2aac construction uses the P2 M Global Theory NB Sys  it succ 2bbb606e2aac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L226-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L226-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow
open GlobalTheory.NB.Sys
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)

theorem P2M_GlobalTheory_NB_Sys__it_succ_2bbb606e2aac (c : ZMod n) (j : ℕ) :
    S.φit c (j + 1) = (S.φl (c + (j : ZMod n) + 1)).comp (S.φit c j) := by sorry

alias «GlobalTheory».«NB».«Sys».«φit_succ» := P2M_GlobalTheory_NB_Sys__it_succ_2bbb606e2aac
