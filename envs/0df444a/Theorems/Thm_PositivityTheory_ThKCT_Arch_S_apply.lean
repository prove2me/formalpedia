-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_S_apply
-- name    : PositivityTheory.ThKCT.Arch.S_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:19.260001+00:00
-- url     : https://prove2.me/theorems/9ea63696-3cd7-47d0-8e59-17a35ec96fe1
-- title:
--   Arch: S apply
-- statement:
--   The Arch construction uses the S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L171-L173

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

theorem PositivityTheory.ThKCT.Arch.S_apply (w : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) (x : V) : S w f x = ph w.2 (w.2 w.1 / 2) x * f (x + w.1) := by sorry
