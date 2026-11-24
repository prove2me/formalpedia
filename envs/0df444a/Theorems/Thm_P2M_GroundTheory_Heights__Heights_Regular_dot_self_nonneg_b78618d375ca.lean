-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca
-- name    : P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:56.833983+00:00
-- url     : https://prove2.me/theorems/dd01c365-00cc-43b1-8ca7-44f58a9f758a
-- title:
--   P2 M Ground Theory Heights  Heights Regular dot self nonneg b78618d375ca: P2 M Ground Theory Heights  Heights Regular dot self nonneg b78618d375ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular dot self nonneg b78618d375ca construction uses the P2 M Ground Theory Heights  Heights Regular dot self nonneg b78618d375ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L15-L16

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

theorem P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca {g : ℕ} (v : Fin g → ℝ) : 0 ≤ v ⬝ᵥ v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«dot_self_nonneg» := P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca
