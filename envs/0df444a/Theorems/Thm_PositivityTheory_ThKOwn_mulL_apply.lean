-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_mulL_apply
-- name    : PositivityTheory.ThKOwn.mulL_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:42.945453+00:00
-- url     : https://prove2.me/theorems/23be0dba-8bb2-4bad-97e1-d1e001418cfc
-- title:
--   Th KOwn: mul L apply
-- statement:
--   The Th KOwn construction uses the mul L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean#L18-L20

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

theorem PositivityTheory.ThKOwn.mulL_apply (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) : mulL L f x = (L x : ℂ) * f x := by sorry
