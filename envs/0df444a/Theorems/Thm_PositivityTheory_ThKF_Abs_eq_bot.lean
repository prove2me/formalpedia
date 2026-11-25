-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Abs_eq_bot
-- name    : PositivityTheory.ThKF.Abs.eq_bot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:40.75413+00:00
-- url     : https://prove2.me/theorems/83fd7596-a43c-47d9-9e47-81e6f6df8323
-- title:
--   Abs: eq bot
-- statement:
--   The Abs construction uses the eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L157-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L157-L176

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem PositivityTheory.ThKF.Abs.eq_bot {St : Submodule ℂ U → Prop} (h : Proj St) (hinf : ∀ s : Set (Submodule ℂ U), (∀ S ∈ s, St S) → St (sInf s))
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N)
    (hu : ∀ M, Maximal (fun P => St P ∧ P ≠ ⊤) M → N ≤ M) : N = ⊥ := by sorry
