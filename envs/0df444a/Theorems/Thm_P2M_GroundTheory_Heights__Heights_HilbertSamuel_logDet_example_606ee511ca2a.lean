-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_logDet_example_606ee511ca2a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_logDet_example_606ee511ca2a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:43.194481+00:00
-- url     : https://prove2.me/theorems/7aaf5252-61b9-5ed9-ba3d-e07ea4561bcf
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel log Det example 606ee511ca2a: P2 M Ground Theory Heights  Heights Hilbert Samuel log Det example 606ee511ca2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel log Det example 606ee511ca2a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel log Det example 606ee511ca2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsLattice.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsLattice.lean#L101-L113

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_logDet_example_606ee511ca2a :
    (∀ t : ℝ, (diagonal fun _ : Fin 2 ↦ ((Real.exp t : ℝ) : ℂ)).PosDef) ∧
    ∀ (t : ℝ) (i j : Fin 2),
      HasDerivAt (fun s : ℝ ↦ diagonal (fun _ : Fin 2 ↦ ((Real.exp s : ℝ) : ℂ)) i j)
        (diagonal (fun _ : Fin 2 ↦ ((Real.exp t : ℝ) : ℂ)) i j) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«logDet_example» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_logDet_example_606ee511ca2a
