-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a
-- name    : P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:03.083803+00:00
-- url     : https://prove2.me/theorems/de105fe5-9bd3-43f9-b970-7b31c8950f37
-- title:
--   P2 M Global Theory Tw Model Phi apply  7c1f3a1c520a: P2 M Global Theory Tw Model Phi apply  7c1f3a1c520a
-- statement:
--   The P2 M Global Theory Tw Model Phi apply  7c1f3a1c520a construction uses the P2 M Global Theory Tw Model Phi apply  7c1f3a1c520a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L13-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
omit [StarRing R]

theorem P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by sorry

alias «GlobalTheory».«Tw».«Model».«Phi_apply'» := P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a
