-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_main
-- name    : PositivityTheory.ThKEst.LinDerPf.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:48.436349+00:00
-- url     : https://prove2.me/theorems/90637f6a-7376-4cb3-b046-e55eca78eade
-- title:
--   Lin Der Pf: main
-- statement:
--   The Lin Der Pf construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L250-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L250-L280

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

theorem PositivityTheory.ThKEst.LinDerPf.main [FiniteDimensional ℝ A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) :
    ∃ (m : ℕ) (Y : Fin m → A) (c : Fin m → A →ₗ[ℝ] ℝ), (∀ i, a (Y i) = -Y i) ∧ ∀ Z : A,
      (∀ t : ℝ, Gr a (NormedSpace.exp (t • Z))) → ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t in 𝓝 (0 : ℝ), NormedSpace.exp (t • Z) = (List.ofFn fun i => NormedSpace.exp (s i t • Y i)).prod := by sorry
