-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_hypotheses_inhabited_686ed1fbed83
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_hypotheses_inhabited_686ed1fbed83
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:20.624093+00:00
-- url     : https://prove2.me/theorems/f3ddd7d3-713c-4aad-aec0-4d31999981c0
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Generic Projection Finite hypotheses inhabited 686ed1fbed83: P2 M Ground Theory Heights  Heights Complex Sets Generic Projection Finite hypotheses inha
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Generic Projection Finite hypotheses inhabited 686ed1fbed83 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Generic Projection Finite hypotheses inhabited 686ed1fbed83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L355-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L355-L360

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_hypotheses_inhabited_686ed1fbed83 :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ)) ∧
      (orthoRows 2 3 ⊆ orthoRows 2 3 ∧ orthoRows 2 3 ⊆ closure (orthoRows 2 3) ∧
        coneProj ∈ orthoRows 2 3) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ Matrix.unitaryGroup (Fin 3) ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«GenericProjectionFinite».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_hypotheses_inhabited_686ed1fbed83
