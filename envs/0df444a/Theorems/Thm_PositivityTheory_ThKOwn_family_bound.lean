-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_family_bound
-- name    : PositivityTheory.ThKOwn.family_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:06:57.229677+00:00
-- url     : https://prove2.me/theorems/e8812878-5924-57b5-8e0e-5734c67c82b4
-- title:
--   Th KOwn: family bound
-- statement:
--   The Th KOwn construction uses the family bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L69-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L69-L93

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

theorem PositivityTheory.ThKOwn.family_bound (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) (z : ℂ) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ expo L Q) (p, x)‖ ≤ C := by sorry
