-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_integrable
-- name    : PositivityTheory.Rg.Sw.HSt.PCD.Good.integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:57.347169+00:00
-- url     : https://prove2.me/theorems/671f5fee-d203-467b-a260-1f84088cc9be
-- title:
--   Good: integrable
-- statement:
--   The Good construction uses the integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L41-L47

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

theorem PositivityTheory.Rg.Sw.HSt.PCD.Good.integrable (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] {x : F} (hx : x ∈ Ω) :
    Integrable (K x) ν := by sorry
