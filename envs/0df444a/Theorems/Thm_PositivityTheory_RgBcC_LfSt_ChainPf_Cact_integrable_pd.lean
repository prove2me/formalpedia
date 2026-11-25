-- Prove2me | Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_integrable_pd
-- name    : PositivityTheory.RgBcC.LfSt.ChainPf.Cact.integrable_pd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:42.090936+00:00
-- url     : https://prove2.me/theorems/bf0c5c28-ce68-4ff5-ac3e-09f7e3148442
-- title:
--   Cact: integrable pd
-- statement:
--   The Cact construction uses the integrable pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ArchimedeanGelfandKernels/LeftEquivariantFunctions/GLMatrixDerivatives/ChainOfCactA.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ArchimedeanGelfandKernels/LeftEquivariantFunctions/GLMatrixDerivatives/ChainOfCactA.lean#L67-L72

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Cact
variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
variable {O : Set H} {OZ : Set Z}
variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}

theorem PositivityTheory.RgBcC.LfSt.ChainPf.Cact.integrable_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x : H} (hx : x ∈ O) :
    Integrable (fun y : Γ => pd Φ (x, ι y)) μ := by sorry
