-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:04.641244+00:00
-- url     : https://prove2.me/theorems/ebc36b9d-99c6-4236-9565-0f1fd31a4658
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound eval pullback d784c0eada3b: P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound eval pullback d784c0eada3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound eval pullback d784c0eada3b construction uses the P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound eval pullback d784c0eada3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreBound.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreBound.lean#L15-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
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
open MvPolynomial
noncomputable section
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (P : MvPolynomial (Fin d) ℂ) :
    eval x (pullback A P) = eval (A.mulVec x) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FibreBound».«eval_pullback» := P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
