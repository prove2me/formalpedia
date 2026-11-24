-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:12.960808+00:00
-- url     : https://prove2.me/theorems/81927194-700b-4bcc-b600-ea2b1d6f545f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act X 5d3e9f420ff7: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act X 5d3e9f420ff7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act X 5d3e9f420ff7 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act X 5d3e9f420ff7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L52-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7 (j : Fin q) : act w (MvPolynomial.X j) = C (w j) * X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«act_X» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7
