-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_smul_of_isHomogeneous_a2658f884797
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_eval_smul_of_isHomogeneous_a2658f884797
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:13.238877+00:00
-- url     : https://prove2.me/theorems/aed9dd7c-1df2-4485-9334-e14c79a7f74c
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets eval smul of is Homogeneous a2658f884797: P2 M Ground Theory Heights  Heights Complex Sets eval smul of is Homogeneous a2658f884797
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets eval smul of is Homogeneous a2658f884797 construction uses the P2 M Ground Theory Heights  Heights Complex Sets eval smul of is Homogeneous a2658f884797 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeScaling.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeScaling.lean#L9-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_eval_smul_of_isHomogeneous_a2658f884797 {n i : ℕ} {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous i)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ i * eval x φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«eval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ComplexSets_eval_smul_of_isHomogeneous_a2658f884797
