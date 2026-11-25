-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NB_Sys__it_zero_9fb129d00d94
-- name    : P2M_GlobalTheory_NB_Sys__it_zero_9fb129d00d94
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:21.714733+00:00
-- url     : https://prove2.me/theorems/2bb214e3-4aed-4214-9372-401cc9d908ea
-- title:
--   P2 M Global Theory NB Sys  it zero 9fb129d00d94: P2 M Global Theory NB Sys  it zero 9fb129d00d94
-- statement:
--   The P2 M Global Theory NB Sys  it zero 9fb129d00d94 construction uses the P2 M Global Theory NB Sys  it zero 9fb129d00d94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L224-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L224-L224

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

theorem P2M_GlobalTheory_NB_Sys__it_zero_9fb129d00d94 (c : ZMod n) : S.φit c 0 = LinearMap.id := by sorry

alias «GlobalTheory».«NB».«Sys».«φit_zero» := P2M_GlobalTheory_NB_Sys__it_zero_9fb129d00d94
