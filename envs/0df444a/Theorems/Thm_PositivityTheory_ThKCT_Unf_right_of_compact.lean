-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Unf_right_of_compact
-- name    : PositivityTheory.ThKCT.Unf.right_of_compact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:45.253794+00:00
-- url     : https://prove2.me/theorems/65e336e0-64b7-411e-950c-64c111ddaba0
-- title:
--   Unf: right of compact
-- statement:
--   The Unf construction uses the right of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/RightOfCompact.lean#L11-L19

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

theorem PositivityTheory.ThKCT.Unf.right_of_compact [CompactSpace G] (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by sorry
