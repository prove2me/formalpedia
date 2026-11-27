-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_fderiv_integral
-- name    : PositivityTheory.Rg.Sw.HSt.PCD.fderiv_integral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:39.439685+00:00
-- url     : https://prove2.me/theorems/a05bb090-e292-46ba-93a3-84632f43aa0c
-- title:
--   PCD: fderiv integral
-- statement:
--   The PCD construction uses the fderiv integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L106-L109

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}

theorem PositivityTheory.Rg.Sw.HSt.PCD.fderiv_integral [CompleteSpace E] (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hK : Good Ω K) {x : F} (hx : x ∈ Ω) :
    fderiv ℝ (fun x => ∫ u, K x u ∂ν) x = ∫ u, fderiv ℝ (K · u) x ∂ν := by sorry
