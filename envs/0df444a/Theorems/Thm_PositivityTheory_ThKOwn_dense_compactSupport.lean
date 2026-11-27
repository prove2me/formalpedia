-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_dense_compactSupport
-- name    : PositivityTheory.ThKOwn.dense_compactSupport
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:08.174907+00:00
-- url     : https://prove2.me/theorems/abd0f3d0-5ee5-54f6-8e60-fea6a6db8733
-- title:
--   Th KOwn: dense compact Support
-- statement:
--   The Th KOwn construction uses the dense compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/DenseC.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/DenseC.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_DenseC
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
open scoped SchwartzMap

theorem PositivityTheory.ThKOwn.dense_compactSupport {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    Dense {f : 𝓢(V, ℂ) | HasCompactSupport (f : V → ℂ)} := by sorry
