-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_common_denom_0a204d048bb4
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_common_denom_0a204d048bb4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:04.00513+00:00
-- url     : https://prove2.me/theorems/3733702b-afce-53ed-89e8-cd83801ea2fb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing exists common denom 0a204d048bb4: P2 M Ground Theory Heights  Heights Chart Vanishing exists common denom 0a204d048bb4
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing exists common denom 0a204d048bb4 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing exists common denom 0a204d048bb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L66-L74

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

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_common_denom_0a204d048bb4 (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {m : ℕ} {u : Fin m → P.FunField} (hu : ∀ j, u j ∈ P.chartRing c) :
    ∃ (E : ℕ) (f : Fin m → MvPolynomial (Coord n) ℤ),
      ∀ j, u j * P.mkF (chartMonomial c 1) ^ E = P.mkF (f j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«exists_common_denom» := P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_common_denom_0a204d048bb4
