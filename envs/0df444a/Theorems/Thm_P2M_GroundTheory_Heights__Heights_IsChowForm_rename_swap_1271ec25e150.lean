-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_rename_swap_1271ec25e150
-- name    : P2M_GroundTheory_Heights__Heights_IsChowForm_rename_swap_1271ec25e150
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:04.114741+00:00
-- url     : https://prove2.me/theorems/d5439bdb-53ea-4e8d-a8d6-18b65db1082a
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form rename swap 1271ec25e150: P2 M Ground Theory Heights  Heights Is Chow Form rename swap 1271ec25e150
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form rename swap 1271ec25e150 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form rename swap 1271ec25e150 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L55-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L55-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsChowForm_rename_swap_1271ec25e150 {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowForm».«rename_swap» := P2M_GroundTheory_Heights__Heights_IsChowForm_rename_swap_1271ec25e150
