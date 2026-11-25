-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_div_chartPow_mem_9fad4a55970a
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_div_chartPow_mem_9fad4a55970a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:52:59.570382+00:00
-- url     : https://prove2.me/theorems/27128070-2b94-5c79-9baf-52c0426ca20a
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun div chart Pow mem 9fad4a55970a: P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun div chart Pow mem 9fad4a55970a
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun div chart Pow mem 9fad4a55970a construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun div chart Pow mem 9fad4a55970a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L74-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_div_chartPow_mem_9fad4a55970a {a : ι → ℤ} (s : IntegralSection P a) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) : s.toFun / P.chartPow c a ∈ P.chartRing c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«toFun_div_chartPow_mem» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_div_chartPow_mem_9fad4a55970a
