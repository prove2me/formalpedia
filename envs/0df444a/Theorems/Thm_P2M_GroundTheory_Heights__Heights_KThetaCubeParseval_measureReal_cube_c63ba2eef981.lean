-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_measureReal_cube_c63ba2eef981
-- name    : P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_measureReal_cube_c63ba2eef981
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:59.118238+00:00
-- url     : https://prove2.me/theorems/bf1e9692-1711-4354-92c4-b28662bc87b5
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Cube Parseval measure Real cube c63ba2eef981: P2 M Ground Theory Heights  Heights KTheta Cube Parseval measure Real cube c63ba2eef981
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Cube Parseval measure Real cube c63ba2eef981 construction uses the P2 M Ground Theory Heights  Heights KTheta Cube Parseval measure Real cube c63ba2eef981 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCubeParseval.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCubeParseval.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval
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
open MeasureTheory Real ComplexConjugate
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCubeParseval

theorem P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_measureReal_cube_c63ba2eef981 (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaCubeParseval».«measureReal_cube» := P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_measureReal_cube_c63ba2eef981
