-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKR_lie__dc6ea91cf961
-- name    : P2M_PositivityTheory_ThKR_lie__dc6ea91cf961
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:23.768195+00:00
-- url     : https://prove2.me/theorems/cef43dcc-b690-522b-97db-5610fab05b8f
-- title:
--   P2 M Positivity Theory Th KR lie  dc6ea91cf961: P2 M Positivity Theory Th KR lie  dc6ea91cf961
-- statement:
--   The P2 M Positivity Theory Th KR lie  dc6ea91cf961 construction uses the P2 M Positivity Theory Th KR lie  dc6ea91cf961 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/ExistsSmoothFun.lean#L190-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/ExistsSmoothFun.lean#L190-L233

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR
variable {l : Type} [Fintype l] [DecidableEq l]

theorem P2M_PositivityTheory_ThKR_lie__dc6ea91cf961 (hL : PositivityTheory.ThKR.LocalLift) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by sorry

alias «PositivityTheory».«ThKR».«lie'» := P2M_PositivityTheory_ThKR_lie__dc6ea91cf961
