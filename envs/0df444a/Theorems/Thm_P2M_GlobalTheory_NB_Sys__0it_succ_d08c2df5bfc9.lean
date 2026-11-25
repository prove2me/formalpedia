-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NB_Sys__0it_succ_d08c2df5bfc9
-- name    : P2M_GlobalTheory_NB_Sys__0it_succ_d08c2df5bfc9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:54.991246+00:00
-- url     : https://prove2.me/theorems/5f071178-3dd3-5c8d-b6b0-ff1d7e192781
-- title:
--   P2 M Global Theory NB Sys  0it succ d08c2df5bfc9: P2 M Global Theory NB Sys  0it succ d08c2df5bfc9
-- statement:
--   The P2 M Global Theory NB Sys  0it succ d08c2df5bfc9 construction uses the P2 M Global Theory NB Sys  0it succ d08c2df5bfc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L293-L294

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
variable [IsDomain O]

theorem P2M_GlobalTheory_NB_Sys__0it_succ_d08c2df5bfc9 (c : ZMod n) (j : ℕ) :
    S.φ0it c (j + 1) = S.φ0 (c + (j : ZMod n) + 1) * S.φ0it c j := by sorry

alias «GlobalTheory».«NB».«Sys».«φ0it_succ» := P2M_GlobalTheory_NB_Sys__0it_succ_d08c2df5bfc9
