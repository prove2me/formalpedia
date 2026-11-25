-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_chartMonomial_mul_chartPow_b6a65f1ac349
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_chartMonomial_mul_chartPow_b6a65f1ac349
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:45.387207+00:00
-- url     : https://prove2.me/theorems/4c2ab038-07ed-4069-8dd7-837b769b9958
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing mk F chart Monomial mul chart Pow b6a65f1ac349: P2 M Ground Theory Heights  Heights Chart Vanishing mk F chart Monomial mul chart Pow b6a65f1ac349
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing mk F chart Monomial mul chart Pow b6a65f1ac349 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing mk F chart Monomial mul chart Pow b6a65f1ac349 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L84-L92

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

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_chartMonomial_mul_chartPow_b6a65f1ac349 {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ (d k + D.deg k).toNat) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«mkF_chartMonomial_mul_chartPow» := P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_chartMonomial_mul_chartPow_b6a65f1ac349
