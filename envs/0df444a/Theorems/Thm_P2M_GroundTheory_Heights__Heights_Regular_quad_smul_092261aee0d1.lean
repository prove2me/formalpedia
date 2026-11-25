-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_smul_092261aee0d1
-- name    : P2M_GroundTheory_Heights__Heights_Regular_quad_smul_092261aee0d1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:29.9186+00:00
-- url     : https://prove2.me/theorems/e3994359-0264-4d12-9c96-55e52e449ff4
-- title:
--   P2 M Ground Theory Heights  Heights Regular quad smul 092261aee0d1: P2 M Ground Theory Heights  Heights Regular quad smul 092261aee0d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular quad smul 092261aee0d1 construction uses the P2 M Ground Theory Heights  Heights Regular quad smul 092261aee0d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_quad_smul_092261aee0d1 {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) (t : ℝ) (v : Fin g → ℝ) :
    (t • v) ⬝ᵥ M *ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ M *ᵥ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«quad_smul» := P2M_GroundTheory_Heights__Heights_Regular_quad_smul_092261aee0d1
