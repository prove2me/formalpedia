-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Holtb_aesm_fderiv
-- name    : PositivityTheory.SiegelWeilFormula.Holtb.aesm_fderiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:36.266085+00:00
-- url     : https://prove2.me/theorems/03985512-58cd-4ff2-8961-fa1ec549dd8e
-- title:
--   Holtb: aesm fderiv
-- statement:
--   The Holtb construction uses the aesm fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/HolomorphicTheta/IntHol.lean#L12-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/HolomorphicTheta/IntHol.lean#L12-L67

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_HolomorphicTheta_IntHol
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
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Holtb
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem PositivityTheory.SiegelWeilFormula.Holtb.aesm_fderiv (f : X → E → ℂ) (W₀ : E) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x, DifferentiableAt ℂ (f x) W₀)
    (hm : ∀ W ∈ ball W₀ r, AEStronglyMeasurable (f · W) ν) :
    AEStronglyMeasurable (fun x => fderiv ℂ (f x) W₀) ν := by sorry
