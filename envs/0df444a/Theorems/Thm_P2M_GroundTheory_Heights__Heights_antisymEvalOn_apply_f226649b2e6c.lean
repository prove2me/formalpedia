-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c
-- name    : P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:54.308866+00:00
-- url     : https://prove2.me/theorems/24c65e35-f90e-465c-8e23-552f0c0ef5d3
-- title:
--   P2 M Ground Theory Heights  Heights antisym Eval On apply f226649b2e6c: P2 M Ground Theory Heights  Heights antisym Eval On apply f226649b2e6c
-- statement:
--   The P2 M Ground Theory Heights  Heights antisym Eval On apply f226649b2e6c construction uses the P2 M Ground Theory Heights  Heights antisym Eval On apply f226649b2e6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ))
    (p : MvPolynomial (T × Fin N) ℝ) (x : Ω) : antisymEvalOn Ω p x = eval (x : T × Fin N → ℝ) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«antisymEvalOn_apply» := P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c

attribute [defeq] P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c
