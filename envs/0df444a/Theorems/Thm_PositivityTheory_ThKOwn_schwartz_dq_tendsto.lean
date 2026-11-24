-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_schwartz_dq_tendsto
-- name    : PositivityTheory.ThKOwn.schwartz_dq_tendsto
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:15:46.332646+00:00
-- url     : https://prove2.me/theorems/5e0a93a6-3786-48ee-836c-60c9d329b2e2
-- title:
--   Th KOwn: schwartz dq tendsto
-- statement:
--   The Th KOwn construction uses the schwartz dq tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/SchwartzDqTendsto.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/SchwartzDqTendsto.lean#L13-L55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_SchwartzDqTendsto
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
open Filter Topology GlobalTheory.CompanionTheory.OM.SchDiff
open scoped SchwartzMap LineDeriv ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem PositivityTheory.ThKOwn.schwartz_dq_tendsto (g : 𝓢(V, ℂ)) (a : V) :
    Tendsto (fun t : ℝ => t⁻¹ • (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g - g)) (𝓝[≠] 0) (𝓝 (∂_{a} g)) := by sorry
