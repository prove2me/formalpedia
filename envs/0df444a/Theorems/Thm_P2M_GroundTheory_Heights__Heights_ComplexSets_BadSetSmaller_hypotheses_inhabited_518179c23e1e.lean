-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_hypotheses_inhabited_518179c23e1e
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_hypotheses_inhabited_518179c23e1e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:18.526824+00:00
-- url     : https://prove2.me/theorems/6c58b3f0-6162-408d-964f-c272b54535b1
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Bad Set Smaller hypotheses inhabited 518179c23e1e: P2 M Ground Theory Heights  Heights Complex Sets Bad Set Smaller hypotheses inhabited 518179c23e1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Bad Set Smaller hypotheses inhabited 518179c23e1e construction uses the P2 M Ground Theory Heights  Heights Complex Sets Bad Set Smaller hypotheses inhabited 518179c23e1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L378-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L378-L381

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_hypotheses_inhabited_518179c23e1e :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧ (X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«BadSetSmaller».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_hypotheses_inhabited_518179c23e1e
