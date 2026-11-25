-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isHomogeneous_dd28bfd9371f
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isHomogeneous_dd28bfd9371f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:00.90853+00:00
-- url     : https://prove2.me/theorems/313a293b-5675-58da-82c0-608dab5614dd
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets cone is Homogeneous dd28bfd9371f: P2 M Ground Theory Heights  Heights Complex Sets cone is Homogeneous dd28bfd9371f
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets cone is Homogeneous dd28bfd9371f construction uses the P2 M Ground Theory Heights  Heights Complex Sets cone is Homogeneous dd28bfd9371f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L321-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L321-L328

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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isHomogeneous_dd28bfd9371f : coneIdeal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«cone_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isHomogeneous_dd28bfd9371f
