-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussShell_base_le_74f8b6676cc1
-- name    : P2M_GroundTheory_Heights__Heights_PGaussShell_base_le_74f8b6676cc1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:44.888815+00:00
-- url     : https://prove2.me/theorems/e095c01d-6e8e-414c-8559-85c707e249f3
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Shell base le 74f8b6676cc1: P2 M Ground Theory Heights  Heights PGauss Shell base le 74f8b6676cc1
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Shell base le 74f8b6676cc1 construction uses the P2 M Ground Theory Heights  Heights PGauss Shell base le 74f8b6676cc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussShell.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussShell.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShell
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
open Real
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussShell

theorem P2M_GroundTheory_Heights__Heights_PGaussShell_base_le_74f8b6676cc1 (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    1 + 2 * (m + 1) / δ ≤ 3 * (m + 1) * (1 + 1 / δ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussShell».«base_le» := P2M_GroundTheory_Heights__Heights_PGaussShell_base_le_74f8b6676cc1
