-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FibreMeasure_measurePreserving_shear_194aa7f5f67c
-- name    : P2M_GroundTheory_Heights__Theta_FibreMeasure_measurePreserving_shear_194aa7f5f67c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:18.704803+00:00
-- url     : https://prove2.me/theorems/b7c56e36-c31b-4d23-bd64-2e5250b1a5ce
-- title:
--   P2 M Ground Theory Heights  Theta Fibre Measure measure Preserving shear 194aa7f5f67c: P2 M Ground Theory Heights  Theta Fibre Measure measure Preserving shear 194aa7f5f67c
-- statement:
--   The P2 M Ground Theory Heights  Theta Fibre Measure measure Preserving shear 194aa7f5f67c construction uses the P2 M Ground Theory Heights  Theta Fibre Measure measure Preserving shear 194aa7f5f67c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/Imports.lean#L14-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/Imports.lean#L14-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FibreMeasure
open MeasureTheory
variable {G P : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [AddCommGroup P] [MeasurableSpace P] [MeasurableAdd₂ P] [MeasurableNeg P]

theorem P2M_GroundTheory_Heights__Theta_FibreMeasure_measurePreserving_shear_194aa7f5f67c (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure P) [ν.IsAddLeftInvariant] [SFinite ν] {B : Set P} (hB : MeasurableSet B)
    (hB0 : ν B ≠ 0) (hBt : ν B ≠ ⊤) (ζ : P →+ G) (hζ : Measurable ζ) (t : G → P)
    (ht : Measurable t) (htζ : ∀ X d, t (X + ζ d) = t X) :
    MeasurePreserving (fun X ↦ X + ζ (t X)) μ μ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FibreMeasure».«measurePreserving_shear» := P2M_GroundTheory_Heights__Theta_FibreMeasure_measurePreserving_shear_194aa7f5f67c
