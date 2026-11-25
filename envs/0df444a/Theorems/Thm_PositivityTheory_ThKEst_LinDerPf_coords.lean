-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_coords
-- name    : PositivityTheory.ThKEst.LinDerPf.coords
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:29.3371+00:00
-- url     : https://prove2.me/theorems/b28c4ebf-e8b7-427d-bd5a-496382fe3cff
-- title:
--   Lin Der Pf: coords
-- statement:
--   The Lin Der Pf construction uses the coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L171-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L171-L230

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}

theorem PositivityTheory.ThKEst.LinDerPf.coords (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {m : ℕ} (Y : Fin m → A) (hY : ∀ i, a (Y i) = -Y i)
    (c : A →L[ℝ] (Fin m → ℝ)) (hc : ∀ s : Fin m → ℝ, c (∑ i, s i • Y i) = s)
    (hc' : ∀ x y, a x = -x → a y = -y → c x = c y → x = y)
    (e : Fin m → ℝ → A) (he : ∀ i, HasStrictDerivAt (e i) (Y i) 0) (he0 : ∀ i, e i 0 = 1) (heG : ∀ i t, Gr a (e i t))
    (g : ℝ → A) (Z : A) (hg : HasDerivAt g Z 0) (hg0 : g 0 = 1) (hgG : ∀ t, Gr a (g t)) :
    ∃ s : ℝ → Fin m → ℝ, s 0 = 0 ∧ HasDerivAt s (c (pr a Z)) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), g t = (List.ofFn fun i => e i (s t i)).prod := by sorry
