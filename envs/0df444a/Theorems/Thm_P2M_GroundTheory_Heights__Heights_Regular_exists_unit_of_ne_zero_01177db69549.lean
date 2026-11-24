-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549
-- name    : P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:37.675023+00:00
-- url     : https://prove2.me/theorems/aec48c17-0886-45a0-ae2c-290964b90a43
-- title:
--   P2 M Ground Theory Heights  Heights Regular exists unit of ne zero 01177db69549: P2 M Ground Theory Heights  Heights Regular exists unit of ne zero 01177db69549
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular exists unit of ne zero 01177db69549 construction uses the P2 M Ground Theory Heights  Heights Regular exists unit of ne zero 01177db69549 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L34-L49

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

theorem P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549 {g : ℕ} {v : Fin g → ℝ} (hv : v ≠ 0) :
    ∃ u ∈ unitSphereDot g, ∀ M : Matrix (Fin g) (Fin g) ℝ,
      v ⬝ᵥ M *ᵥ v = (v ⬝ᵥ v) * (u ⬝ᵥ M *ᵥ u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«exists_unit_of_ne_zero» := P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549
