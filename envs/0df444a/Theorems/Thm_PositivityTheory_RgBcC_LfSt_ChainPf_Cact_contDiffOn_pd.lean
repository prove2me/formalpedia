-- Prove2me | Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_contDiffOn_pd
-- name    : PositivityTheory.RgBcC.LfSt.ChainPf.Cact.contDiffOn_pd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:39.320621+00:00
-- url     : https://prove2.me/theorems/4884d21e-b427-4dca-8377-a2e8a1d88bcc
-- title:
--   Cact: cont Diff On pd
-- statement:
--   The Cact construction uses the cont Diff On pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ArchimedeanGelfandKernels/LeftEquivariantFunctions/GLMatrixDerivatives/ChainOfCactA.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ArchimedeanGelfandKernels/LeftEquivariantFunctions/GLMatrixDerivatives/ChainOfCactA.lean#L23-L26

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

theorem PositivityTheory.RgBcC.LfSt.ChainPf.Cact.contDiffOn_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) : ContDiffOn ℝ ∞ (pd Φ) (O ×ˢ OZ) := by sorry
