-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_hyps_79c8a84da216
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_line_hyps_79c8a84da216
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:13.486048+00:00
-- url     : https://prove2.me/theorems/2dc7ef3b-cad3-4942-a6bb-faa6b1146fbc
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets line hyps 79c8a84da216: P2 M Ground Theory Heights  Heights Complex Sets line hyps 79c8a84da216
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets line hyps 79c8a84da216 construction uses the P2 M Ground Theory Heights  Heights Complex Sets line hyps 79c8a84da216 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L350-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L350-L353

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_line_hyps_79c8a84da216 : (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
    ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (1 : ℕ) ∧
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«line_hyps» := P2M_GroundTheory_Heights__Heights_ComplexSets_line_hyps_79c8a84da216
