-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NB_Sys__0it_zero_cfda2f013b18
-- name    : P2M_GlobalTheory_NB_Sys__0it_zero_cfda2f013b18
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:26.079036+00:00
-- url     : https://prove2.me/theorems/db423181-2e0f-4aa4-b2d5-346736fca1c0
-- title:
--   P2 M Global Theory NB Sys  0it zero cfda2f013b18: P2 M Global Theory NB Sys  0it zero cfda2f013b18
-- statement:
--   The P2 M Global Theory NB Sys  0it zero cfda2f013b18 construction uses the P2 M Global Theory NB Sys  0it zero cfda2f013b18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L291-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L291-L291

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

theorem P2M_GlobalTheory_NB_Sys__0it_zero_cfda2f013b18 (c : ZMod n) : S.φ0it c 0 = 1 := by sorry

alias «GlobalTheory».«NB».«Sys».«φ0it_zero» := P2M_GlobalTheory_NB_Sys__0it_zero_cfda2f013b18
