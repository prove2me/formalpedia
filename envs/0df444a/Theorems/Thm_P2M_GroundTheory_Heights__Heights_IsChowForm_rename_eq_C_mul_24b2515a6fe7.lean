-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_rename_eq_C_mul_24b2515a6fe7
-- name    : P2M_GroundTheory_Heights__Heights_IsChowForm_rename_eq_C_mul_24b2515a6fe7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:03.76996+00:00
-- url     : https://prove2.me/theorems/6c670688-e575-461d-93b7-011633aec2da
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form rename eq C mul 24b2515a6fe7: P2 M Ground Theory Heights  Heights Is Chow Form rename eq C mul 24b2515a6fe7
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form rename eq C mul 24b2515a6fe7 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form rename eq C mul 24b2515a6fe7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L39-L53

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

theorem P2M_GroundTheory_Heights__Heights_IsChowForm_rename_eq_C_mul_24b2515a6fe7 {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowForm».«rename_eq_C_mul» := P2M_GroundTheory_Heights__Heights_IsChowForm_rename_eq_C_mul_24b2515a6fe7
