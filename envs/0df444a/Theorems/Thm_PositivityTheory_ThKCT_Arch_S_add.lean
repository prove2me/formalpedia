-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_S_add
-- name    : PositivityTheory.ThKCT.Arch.S_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:28.531593+00:00
-- url     : https://prove2.me/theorems/7d027bbd-4fb5-4502-95c4-571ceaf72389
-- title:
--   Arch: S add
-- statement:
--   The Arch construction uses the S add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L226-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L226-L234

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

theorem PositivityTheory.ThKCT.Arch.S_add (w h : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) :
    S (w + h) f = cexp (I * ((w.2 h.1 - h.2 w.1) / 2 : ℝ)) • S w (S h f) := by sorry
