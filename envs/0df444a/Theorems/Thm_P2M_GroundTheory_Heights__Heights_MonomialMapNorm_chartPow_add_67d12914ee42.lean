-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:48.989811+00:00
-- url     : https://prove2.me/theorems/830694e2-64e3-4e16-aa8f-39d859b2e73b
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow add 67d12914ee42: P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow add 67d12914ee42
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow add 67d12914ee42 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow add 67d12914ee42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L48-L51

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a b : ι → ℤ) :
    P.chartPow c (a + b) = P.chartPow c a * P.chartPow c b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«chartPow_add» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42
