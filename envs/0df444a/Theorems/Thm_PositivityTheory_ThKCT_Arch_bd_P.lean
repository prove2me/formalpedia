-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_bd_P
-- name    : PositivityTheory.ThKCT.Arch.bd_P
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:58.387799+00:00
-- url     : https://prove2.me/theorems/4bcac1df-0326-449e-9dbc-249d5dbef091
-- title:
--   Arch: bd P
-- statement:
--   The Arch construction uses the bd P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L30-L31

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

theorem PositivityTheory.ThKCT.Arch.bd_P (m : ℕ) (f : SchwartzMap V ℂ) : Bd m f (2 ^ m * P V m f) := by sorry
