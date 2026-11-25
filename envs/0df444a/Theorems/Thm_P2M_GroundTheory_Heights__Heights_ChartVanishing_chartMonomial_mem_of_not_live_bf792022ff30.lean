-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_chartMonomial_mem_of_not_live_bf792022ff30
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_chartMonomial_mem_of_not_live_bf792022ff30
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:45.882408+00:00
-- url     : https://prove2.me/theorems/8be0159a-dd3f-5af1-a839-3eca7f987076
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing chart Monomial mem of not live bf792022ff30: P2 M Ground Theory Heights  Heights Chart Vanishing chart Monomial mem of not live bf792022ff30
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing chart Monomial mem of not live bf792022ff30 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing chart Monomial mem of not live bf792022ff30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L28-L33

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

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_chartMonomial_mem_of_not_live_bf792022ff30 (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«chartMonomial_mem_of_not_live» := P2M_GroundTheory_Heights__Heights_ChartVanishing_chartMonomial_mem_of_not_live_bf792022ff30
