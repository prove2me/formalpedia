-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussPoissonDual_proof_df0a7873f0f1
-- name    : P2M_GroundTheory_Heights__Heights_GaussPoissonDual_proof_df0a7873f0f1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:45.640328+00:00
-- url     : https://prove2.me/theorems/fbee9888-0661-4edd-81a5-14b9371e47ec
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Poisson Dual proof df0a7873f0f1: P2 M Ground Theory Heights  Heights Gauss Poisson Dual proof df0a7873f0f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Poisson Dual proof df0a7873f0f1 construction uses the P2 M Ground Theory Heights  Heights Gauss Poisson Dual proof df0a7873f0f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonDual.lean#L25-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonDual.lean#L25-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonDual
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
open Matrix Real
noncomputable section
open PGaussPoissonDual

theorem P2M_GroundTheory_Heights__Heights_GaussPoissonDual_proof_df0a7873f0f1 (hS : GaussSqrt.Statement) (hP : GaussPoissonBound.Statement)
    (hM : GaussDualMin.Statement) (hD : GaussDetFactor.Statement) :
    GaussPoissonDual.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussPoissonDual».«proof» := P2M_GroundTheory_Heights__Heights_GaussPoissonDual_proof_df0a7873f0f1
