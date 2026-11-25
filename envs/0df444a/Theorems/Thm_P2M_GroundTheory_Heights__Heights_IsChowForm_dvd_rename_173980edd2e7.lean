-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_dvd_rename_173980edd2e7
-- name    : P2M_GroundTheory_Heights__Heights_IsChowForm_dvd_rename_173980edd2e7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:02.44566+00:00
-- url     : https://prove2.me/theorems/03f24ba5-dcca-43ad-aeb9-1ac0e16d0a8e
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form dvd rename 173980edd2e7: P2 M Ground Theory Heights  Heights Is Chow Form dvd rename 173980edd2e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form dvd rename 173980edd2e7 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form dvd rename 173980edd2e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L20-L24

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

theorem P2M_GroundTheory_Heights__Heights_IsChowForm_dvd_rename_173980edd2e7 {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowForm».«dvd_rename» := P2M_GroundTheory_Heights__Heights_IsChowForm_dvd_rename_173980edd2e7
