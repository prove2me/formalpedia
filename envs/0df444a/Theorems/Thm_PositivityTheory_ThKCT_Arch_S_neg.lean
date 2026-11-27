-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_S_neg
-- name    : PositivityTheory.ThKCT.Arch.S_neg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:46.598427+00:00
-- url     : https://prove2.me/theorems/0b6eb15e-cbb9-5b5b-95e5-a9b0d19def4b
-- title:
--   Arch: S neg
-- statement:
--   The Arch construction uses the S neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L236-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L236-L239

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

theorem PositivityTheory.ThKCT.Arch.S_neg (w : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) : S w (S (-w) f) = f := by sorry
