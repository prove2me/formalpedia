-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_nat
-- name    : PositivityTheory.Rg.Sw.HSt.PCD.contDiffOn_nat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:09.220429+00:00
-- url     : https://prove2.me/theorems/07769401-d939-478d-bf30-6e70e0cf8d15
-- title:
--   PCD: cont Diff On nat
-- statement:
--   The PCD construction uses the cont Diff On nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L86-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L86-L100

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
omit [NormedSpace ℝ E]

theorem PositivityTheory.Rg.Sw.HSt.PCD.contDiffOn_nat (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (N : ℕ) :
    ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (K : F → X → E'), Good Ω K →
      ContDiffOn ℝ N (fun x => ∫ u, K x u ∂ν) Ω := by sorry
