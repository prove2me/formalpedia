-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:40.720671+00:00
-- url     : https://prove2.me/theorems/25f8c968-3009-460f-8d53-f5108b1aaa30
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists monic d58be7e7bc4c: P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists monic d58be7e7bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists monic d58be7e7bc4c construction uses the P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster exists monic d58be7e7bc4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L23-L36

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (j : Fin n) :
    ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧
      ∀ x ∈ zeroSet J, (P.map (eval (A.mulVec x))).IsRoot (x j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FiniteProjectionCluster».«exists_monic» := P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c
