-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_family_deriv
-- name    : PositivityTheory.ThKOwn.family_deriv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:38.262532+00:00
-- url     : https://prove2.me/theorems/e1b280d8-d70d-4355-93a2-3fb894a1ba28
-- title:
--   Th KOwn: family deriv
-- statement:
--   The Th KOwn construction uses the family deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L95-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L95-L114

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

theorem PositivityTheory.ThKOwn.family_deriv (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2)
    {G : ℂ → 𝓢(V, ℂ)} (hG : ∀ z, ⇑(G z) = fun x => (cexp ∘ expo L Q) (z, x)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    HasDerivAt (fun p => T (G p)) (T (mulL L (G z))) z := by sorry
