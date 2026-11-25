-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Unf_conv_eq
-- name    : PositivityTheory.ThKCT.Unf.conv_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:37.093541+00:00
-- url     : https://prove2.me/theorems/bf8554c6-a300-45e5-8386-ed8e4157f1d4
-- title:
--   Unf: conv eq
-- statement:
--   The Unf construction uses the conv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L24-L43

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
omit [T2Space G]

theorem PositivityTheory.ThKCT.Unf.conv_eq (hP : ∀ p ∈ P, m.map (p * ·) = m) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) {f b : G → ℝ≥0∞}
    (hf : Measurable f) (hb : Measurable b) (hbK : ∀ g, ∀ k ∈ K, b (g * k) = b g) :
    ∫⁻ g, b g * ∫⁻ x, f (x * g) ∂m ∂ν = (∫⁻ x, b x⁻¹ ∂m) * ∫⁻ g, f g ∂ν := by sorry
