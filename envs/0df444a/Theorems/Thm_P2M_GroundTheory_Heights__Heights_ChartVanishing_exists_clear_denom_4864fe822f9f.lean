-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_clear_denom_4864fe822f9f
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_clear_denom_4864fe822f9f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:57.829328+00:00
-- url     : https://prove2.me/theorems/8f007071-5b72-59f0-bd46-f1428bfe6c63
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing exists clear denom 4864fe822f9f: P2 M Ground Theory Heights  Heights Chart Vanishing exists clear denom 4864fe822f9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing exists clear denom 4864fe822f9f construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing exists clear denom 4864fe822f9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L35-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L35-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_clear_denom_4864fe822f9f (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«exists_clear_denom» := P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_clear_denom_4864fe822f9f
