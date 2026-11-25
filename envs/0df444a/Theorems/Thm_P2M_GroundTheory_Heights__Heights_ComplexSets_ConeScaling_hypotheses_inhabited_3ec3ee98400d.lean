-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_hypotheses_inhabited_3ec3ee98400d
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_hypotheses_inhabited_3ec3ee98400d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:02.36642+00:00
-- url     : https://prove2.me/theorems/2bdde66f-9651-41e7-9dd4-018202b0e5f4
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Cone Scaling hypotheses inhabited 3ec3ee98400d: P2 M Ground Theory Heights  Heights Complex Sets Cone Scaling hypotheses inhabited 3ec3ee98400d
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Cone Scaling hypotheses inhabited 3ec3ee98400d construction uses the P2 M Ground Theory Heights  Heights Complex Sets Cone Scaling hypotheses inhabited 3ec3ee98400d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L384-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L384-L386

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_hypotheses_inhabited_3ec3ee98400d :
    coneIdeal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) ∧ (2 : ℂ) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«ConeScaling».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_hypotheses_inhabited_3ec3ee98400d
