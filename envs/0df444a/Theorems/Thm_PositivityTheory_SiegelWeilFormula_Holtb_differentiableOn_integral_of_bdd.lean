-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Holtb_differentiableOn_integral_of_bdd
-- name    : PositivityTheory.SiegelWeilFormula.Holtb.differentiableOn_integral_of_bdd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:30.191996+00:00
-- url     : https://prove2.me/theorems/ef2b81bf-6416-5997-930c-f831f475de1b
-- title:
--   Holtb: differentiable On integral of bdd
-- statement:
--   The Holtb construction uses the differentiable On integral of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/HolomorphicTheta/IntHol.lean#L69-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/HolomorphicTheta/IntHol.lean#L69-L105

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

theorem PositivityTheory.SiegelWeilFormula.Holtb.differentiableOn_integral_of_bdd [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (f : X → E → ℂ)
    (hd : ∀ x, DifferentiableOn ℂ (f x) U) (hm : ∀ W ∈ U, AEStronglyMeasurable (f · W) ν)
    (hb : ∀ W₀ ∈ U, ∃ r > 0, ∃ M, ball W₀ r ⊆ U ∧ ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M) :
    DifferentiableOn ℂ (fun W => ∫ x, f x W ∂ν) U := by sorry
