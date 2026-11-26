-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_mulL_pow_apply
-- name    : PositivityTheory.ThKOwn.mulL_pow_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:34.574367+00:00
-- url     : https://prove2.me/theorems/ecd1eb6d-f5bb-4285-9a3e-00a09ac495c0
-- title:
--   Th KOwn: mul L pow apply
-- statement:
--   The Th KOwn construction uses the mul L pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L22-L25

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

theorem PositivityTheory.ThKOwn.mulL_pow_apply (L : V →L[ℝ] ℝ) (m : ℕ) (f : 𝓢(V, ℂ)) (x : V) : (mulL L ^ m) f x = (L x : ℂ) ^ m * f x := by sorry
