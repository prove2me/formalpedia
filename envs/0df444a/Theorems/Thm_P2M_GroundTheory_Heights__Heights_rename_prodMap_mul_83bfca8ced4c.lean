-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rename_prodMap_mul_83bfca8ced4c
-- name    : P2M_GroundTheory_Heights__Heights_rename_prodMap_mul_83bfca8ced4c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:26.402825+00:00
-- url     : https://prove2.me/theorems/4875ebc9-63b7-4a17-8f41-c945725ca1d4
-- title:
--   P2 M Ground Theory Heights  Heights rename prod Map mul 83bfca8ced4c: P2 M Ground Theory Heights  Heights rename prod Map mul 83bfca8ced4c
-- statement:
--   The P2 M Ground Theory Heights  Heights rename prod Map mul 83bfca8ced4c construction uses the P2 M Ground Theory Heights  Heights rename prod Map mul 83bfca8ced4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_rename_prodMap_mul_83bfca8ced4c (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rename_prodMap_mul» := P2M_GroundTheory_Heights__Heights_rename_prodMap_mul_83bfca8ced4c
