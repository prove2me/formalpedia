-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:19.509958+00:00
-- url     : https://prove2.me/theorems/090da604-332a-43ee-b13b-d8f8678ea160
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing mk F X ne zero f0798c5f09f9: P2 M Ground Theory Heights  Heights Chart Vanishing mk F X ne zero f0798c5f09f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing mk F X ne zero f0798c5f09f9 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing mk F X ne zero f0798c5f09f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L24-L26

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9 (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«mkF_X_ne_zero» := P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9
