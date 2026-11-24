-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_apply
-- name    : PositivityTheory.ThKCT.Arch.sc_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:17.45156+00:00
-- url     : https://prove2.me/theorems/47b6b77d-6a84-49a6-bb22-dfa784c7a949
-- title:
--   Arch: sc apply
-- statement:
--   The Arch construction uses the sc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L23-L24

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem PositivityTheory.ThKCT.Arch.sc_apply {Z : Type} [AddCommGroup Z] [Module ℂ Z] {C : ℝ} (h : 0 ≤ C) (p : Seminorm ℂ Z) (f : Z) : sc C p f = C * p f := by sorry
