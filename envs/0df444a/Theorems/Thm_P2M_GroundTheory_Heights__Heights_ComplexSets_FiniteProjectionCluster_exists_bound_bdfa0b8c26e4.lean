-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_bound_bdfa0b8c26e4
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_bound_bdfa0b8c26e4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:32.984584+00:00
-- url     : https://prove2.me/theorems/985d4d66-a039-453c-92ee-c346d8f74d5e
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists bound bdfa0b8c26e4: P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists bound bdfa0b8c26
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists bound bdfa0b8c26e4 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists bound bdfa0b8c26e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L38-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L38-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
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
open MvPolynomial Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_bound_bdfa0b8c26e4 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (c : Fin d → ℂ) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ zeroSet J, dist (A.mulVec x) c ≤ R → ‖x‖ ≤ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FiniteProjectionCluster».«exists_bound» := P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_bound_bdfa0b8c26e4
