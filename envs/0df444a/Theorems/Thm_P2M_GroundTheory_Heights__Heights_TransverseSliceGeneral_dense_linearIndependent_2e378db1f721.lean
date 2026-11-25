-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_dense_linearIndependent_2e378db1f721
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_dense_linearIndependent_2e378db1f721
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:46.146806+00:00
-- url     : https://prove2.me/theorems/914178c2-5304-5613-a615-a917a180c082
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General dense linear Independent 2e378db1f721: P2 M Ground Theory Heights  Heights Transverse Slice General dense linear Independent 2e378db1f721
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General dense linear Independent 2e378db1f721 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General dense linear Independent 2e378db1f721 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L137-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L137-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_dense_linearIndependent_2e378db1f721 {m d : ℕ} (h : m ≤ d) :
    Dense {f : Fin m → Fin d → ℂ | LinearIndependent ℂ f} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«dense_linearIndependent» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_dense_linearIndependent_2e378db1f721
