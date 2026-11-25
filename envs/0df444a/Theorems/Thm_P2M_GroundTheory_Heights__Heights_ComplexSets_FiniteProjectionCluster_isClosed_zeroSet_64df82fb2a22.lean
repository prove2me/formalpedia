-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_isClosed_zeroSet_64df82fb2a22
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_isClosed_zeroSet_64df82fb2a22
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:22.225553+00:00
-- url     : https://prove2.me/theorems/ecdd65b2-3758-55e5-9ef9-84f7a5592230
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster is Closed zero Set 64df82fb2a22: P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster is Closed zero Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster is Closed zero Set 64df82fb2a22 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Finite Projection Cluster is Closed zero Set 64df82fb2a22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionCluster.lean#L17-L21

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_isClosed_zeroSet_64df82fb2a22 (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FiniteProjectionCluster».«isClosed_zeroSet» := P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_isClosed_zeroSet_64df82fb2a22
