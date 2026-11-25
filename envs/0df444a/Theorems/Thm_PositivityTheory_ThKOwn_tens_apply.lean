-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_tens_apply
-- name    : PositivityTheory.ThKOwn.tens_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:11.066496+00:00
-- url     : https://prove2.me/theorems/c99e7673-892c-5c7c-9440-4868828ccbe0
-- title:
--   Th KOwn: tens apply
-- statement:
--   The Th KOwn construction uses the tens apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/NormIterComp.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/NormIterComp.lean#L57-L57

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_NormIterComp
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
open scoped SchwartzMap ContDiff
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem PositivityTheory.ThKOwn.tens_apply (φ : 𝓢(A, ℂ)) (f : 𝓢(B, ℂ)) (a : A) (b : B) : tens φ f (WithLp.toLp 2 (a, b)) = φ a * f b := by sorry
