-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:53.008284+00:00
-- url     : https://prove2.me/theorems/351c5309-bf47-4bb0-803c-5d4e84142c52
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster fibre finite 7d46f66826ee: P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster fibre finite 7d46f66826
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster fibre finite 7d46f66826ee construction uses the P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster fibre finite 7d46f66826ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L61-L71

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (y : Fin d → ℂ) :
    {x | x ∈ zeroSet J ∧ A.mulVec x = y}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FiniteProjectionCluster».«fibre_finite» := P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
