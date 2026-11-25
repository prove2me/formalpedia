-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Unf_cont_M
-- name    : PositivityTheory.ThKCT.Unf.cont_M
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:38.449905+00:00
-- url     : https://prove2.me/theorems/5165a4f4-d504-4dee-92ac-f31bb6f96ab6
-- title:
--   Unf: cont M
-- statement:
--   The Unf construction uses the cont M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L46-L57

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}
omit [SFinite m]

theorem PositivityTheory.ThKCT.Unf.cont_M [IsFiniteMeasureOnCompacts m] {f : G → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) (h0 : 0 ≤ f) :
    Continuous fun g => ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m := by sorry
