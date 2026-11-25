-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_cross_mem_of_live_a5ef6372da62
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_cross_mem_of_live_a5ef6372da62
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:51.557893+00:00
-- url     : https://prove2.me/theorems/73994a57-ee23-517b-b0fb-45967fcfbfa1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing cross mem of live a5ef6372da62: P2 M Ground Theory Heights  Heights Chart Vanishing cross mem of live a5ef6372da62
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing cross mem of live a5ef6372da62 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing cross mem of live a5ef6372da62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L76-L82

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

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_cross_mem_of_live_a5ef6372da62 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {c c' : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (hc' : P.IsLive c')
    (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«cross_mem_of_live» := P2M_GroundTheory_Heights__Heights_ChartVanishing_cross_mem_of_live_a5ef6372da62
