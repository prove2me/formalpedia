-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_expo_re
-- name    : PositivityTheory.ThKOwn.expo_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:41.318026+00:00
-- url     : https://prove2.me/theorems/eac5e6d3-aa1d-4ff4-89b9-c7dea423ed3f
-- title:
--   Th KOwn: expo re
-- statement:
--   The Th KOwn construction uses the expo re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L34-L50

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

theorem PositivityTheory.ThKOwn.expo_re (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) {R : ℝ} {p : ℂ} (hp : ‖p‖ ≤ R) (x : V) :
    (expo L Q (p, x)).re ≤ (R * ‖L‖) ^ 2 / (2 * w) + -(w / 2) * ‖x‖ ^ 2 := by sorry
