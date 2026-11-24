-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThetaBound_proof_c7e8ddff0701
-- name    : P2M_GroundTheory_Heights__Heights_ThetaBound_proof_c7e8ddff0701
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:06.890919+00:00
-- url     : https://prove2.me/theorems/5951dba9-b9aa-4ffa-9c20-a99146c37a3d
-- title:
--   P2 M Ground Theory Heights  Heights Theta Bound proof c7e8ddff0701: P2 M Ground Theory Heights  Heights Theta Bound proof c7e8ddff0701
-- statement:
--   The P2 M Ground Theory Heights  Heights Theta Bound proof c7e8ddff0701 construction uses the P2 M Ground Theory Heights  Heights Theta Bound proof c7e8ddff0701 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaTop.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaTop.lean#L9-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaTop
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

theorem P2M_GroundTheory_Heights__Heights_ThetaBound_proof_c7e8ddff0701 (hG : GaussianSum.Statement) (hMean : ThetaMean.Statement)
    (hMaj : ThetaNormMajorant.Statement) (hSplit : ThetaFirstCoordSplit.Statement)
    (hConst : ThetaConstants.Statement) : ThetaBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ThetaBound».«proof» := P2M_GroundTheory_Heights__Heights_ThetaBound_proof_c7e8ddff0701
