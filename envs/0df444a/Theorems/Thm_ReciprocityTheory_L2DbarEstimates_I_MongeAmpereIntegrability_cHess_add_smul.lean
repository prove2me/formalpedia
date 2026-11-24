-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cHess_add_smul
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:15.433318+00:00
-- url     : https://prove2.me/theorems/f6293de8-f85d-46d0-b221-4726820035ac
-- title:
--   Monge Ampere Integrability: c Hess add smul
-- statement:
--   The Monge Ampere Integrability construction uses the c Hess add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L49-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L49-L76

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul {Ω : Set (V n)} (hΩ : IsOpen Ω) {p q : V n → ℝ}
    (hp : ContDiffOn ℝ ∞ p Ω) (hq : ContDiffOn ℝ ∞ q Ω) (t : ℝ) {y : V n} (hy : y ∈ Ω) :
    cHess n (fun w => ((p w + t * q w : ℝ) : ℂ)) y =
      cHess n (fun w => (p w : ℂ)) y + (t : ℂ) • cHess n (fun w => (q w : ℂ)) y := by sorry
