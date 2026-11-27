-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_kill_exp
-- name    : PositivityTheory.ThKOwn.kill_exp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:43.10813+00:00
-- url     : https://prove2.me/theorems/674e6d13-c1df-4a08-8a76-3e0999cb9653
-- title:
--   Th KOwn: kill exp
-- statement:
--   The Th KOwn construction uses the kill exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L116-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L116-L139

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open Filter Topology Complex GlobalTheory.CompanionTheory.OM.SchDiff GlobalTheory.CompanionTheory.OM.GaussSch
open scoped SchwartzMap ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (L : V →L[ℝ] ℝ) {Q : V → ℂ} {w : ℝ}

theorem PositivityTheory.ThKOwn.kill_exp (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2)
    {g : 𝓢(V, ℂ)} (hg : ∀ x, g x = cexp (Q x)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (hT : ∀ m : ℕ, T ((mulL L ^ m) g) = 0)
    (z : ℂ) {f : 𝓢(V, ℂ)} (hf : ∀ x, f x = cexp (z * (L x : ℂ)) * g x) : T f = 0 := by sorry
