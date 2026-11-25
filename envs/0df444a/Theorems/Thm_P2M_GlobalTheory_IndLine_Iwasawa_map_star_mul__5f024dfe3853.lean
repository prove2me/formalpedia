-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_map_star_mul__5f024dfe3853
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_map_star_mul__5f024dfe3853
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:50.246826+00:00
-- url     : https://prove2.me/theorems/224d2f76-e3a6-4c71-88f4-d5c783584bb8
-- title:
--   P2 M Global Theory Ind Line Iwasawa map star mul  5f024dfe3853: P2 M Global Theory Ind Line Iwasawa map star mul  5f024dfe3853
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa map star mul  5f024dfe3853 construction uses the P2 M Global Theory Ind Line Iwasawa map star mul  5f024dfe3853 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L133-L135

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
variable {m : Type} [Fintype m] [DecidableEq m]

theorem P2M_GlobalTheory_IndLine_Iwasawa_map_star_mul__5f024dfe3853 {m n p : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (A * B).map star = A.map star * B.map star := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«map_star_mul'» := P2M_GlobalTheory_IndLine_Iwasawa_map_star_mul__5f024dfe3853
