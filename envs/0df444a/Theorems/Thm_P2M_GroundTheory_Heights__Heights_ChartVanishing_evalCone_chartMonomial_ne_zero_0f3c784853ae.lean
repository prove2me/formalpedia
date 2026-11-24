-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:45.537874+00:00
-- url     : https://prove2.me/theorems/4867f1d6-43ce-4318-9b2b-e62a818a66d9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing eval Cone chart Monomial ne zero 0f3c784853ae: P2 M Ground Theory Heights  Heights Chart Vanishing eval Cone chart Monomial ne zero 0f3c784853ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing eval Cone chart Monomial ne zero 0f3c784853ae construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing eval Cone chart Monomial ne zero 0f3c784853ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L96-L99

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hz : ∀ k, z k (c k) ≠ 0) (e : ι → ℕ) : evalCone z (chartMonomial c e) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«evalCone_chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae
