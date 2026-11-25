-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_isFiniteProjection_3268c8fd7565
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_line_isFiniteProjection_3268c8fd7565
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:28.625297+00:00
-- url     : https://prove2.me/theorems/0c5c7451-c2eb-4ab5-9b27-ebc025f2f90d
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets line is Finite Projection 3268c8fd7565: P2 M Ground Theory Heights  Heights Complex Sets line is Finite Projection 3268c8fd7565
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets line is Finite Projection 3268c8fd7565 construction uses the P2 M Ground Theory Heights  Heights Complex Sets line is Finite Projection 3268c8fd7565 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L109-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_line_isFiniteProjection_3268c8fd7565 :
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«line_isFiniteProjection» := P2M_GroundTheory_Heights__Heights_ComplexSets_line_isFiniteProjection_3268c8fd7565
