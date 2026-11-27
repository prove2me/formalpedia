-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_packing_example_4d57666d7620
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_packing_example_4d57666d7620
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:36.874061+00:00
-- url     : https://prove2.me/theorems/70dddd24-dd4a-5a16-8fe7-d6b5f3989f74
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel packing example 4d57666d7620: P2 M Ground Theory Heights  Heights Hilbert Samuel packing example 4d57666d7620
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel packing example 4d57666d7620 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel packing example 4d57666d7620 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsLattice.lean#L204-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsLattice.lean#L204-L230

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_packing_example_4d57666d7620 :
    let S : Finset (EuclideanSpace ℝ (Fin 2)) := {0, EuclideanSpace.basisFun (Fin 2) ℝ 0}
    (∀ s ∈ S, s ∈ standardLattice) ∧ (∀ s ∈ S, ‖s‖ ≤ 1) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Real.exp (-0) ≤ ‖s - t‖) ∧ S.card = 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«packing_example» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_packing_example_4d57666d7620
