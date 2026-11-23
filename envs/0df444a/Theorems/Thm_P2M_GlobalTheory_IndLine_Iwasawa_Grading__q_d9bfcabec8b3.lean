-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:13.2728+00:00
-- url     : https://prove2.me/theorems/90600579-bcac-4fef-ac55-7200309d9df9
-- title:
--   P2 M Global Theory Ind Line Iwasawa Grading  q d9bfcabec8b3: P2 M Global Theory Ind Line Iwasawa Grading  q d9bfcabec8b3
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Grading  q d9bfcabec8b3 construction uses the P2 M Global Theory Ind Line Iwasawa Grading  q d9bfcabec8b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L85-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {R : Type} [Ring R]
open GlobalTheory.IndLine.Iwasawa.Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h

theorem P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3 : θ * q = p * θ := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Grading».«θq» := P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3
