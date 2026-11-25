-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_chain
-- name    : PositivityTheory.ThKEst.LinDerPf.chain
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:11.630094+00:00
-- url     : https://prove2.me/theorems/4be1ab8b-2f7d-58ff-9b37-20ab6908b6f9
-- title:
--   Lin Der Pf: chain
-- statement:
--   The Lin Der Pf construction uses the chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L73-L93

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
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem PositivityTheory.ThKEst.LinDerPf.chain (f : H → ℂ) : ∀ (m : ℕ) (β : Fin m → Multiplicative ℝ →* H) (_ : ∀ i, Continuous (β i))
    (f' : Fin m → H → ℂ) (_ : ∀ i, Continuous (f' i))
    (_ : ∀ i h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0)
    (p : ℝ → H) (_ : ContinuousAt p 0) (u : Fin m → ℝ → ℝ) (u' : Fin m → ℝ) (_ : ∀ i, HasDerivAt (u i) (u' i) 0)
    (_ : ∀ i, u i 0 = 0) (D : ℂ) (_ : HasDerivAt (fun t => f (p t)) D 0),
    HasDerivAt (fun t => f (p t * (List.ofFn fun i => β i (Multiplicative.ofAdd (u i t))).prod))
      (D + ∑ i, (u' i : ℂ) * f' i (p 0)) 0 := by sorry
