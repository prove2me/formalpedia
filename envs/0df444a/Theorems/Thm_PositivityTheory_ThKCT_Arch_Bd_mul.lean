-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_mul
-- name    : PositivityTheory.ThKCT.Arch.Bd.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:21.920792+00:00
-- url     : https://prove2.me/theorems/82e03751-cfdc-4e87-be67-3965255171f3
-- title:
--   Bd: mul
-- statement:
--   The Bd construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L93-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L93-L114

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

theorem PositivityTheory.ThKCT.Arch.Bd.mul {m r : ℕ} {a f : V → ℂ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) {A C : ℝ}
    (hA : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ A * (1 + ‖x‖) ^ r) (h : Bd (m + r) f C) :
    Bd m (fun x => a x * f x) (2 ^ m * (A * C)) := by sorry
