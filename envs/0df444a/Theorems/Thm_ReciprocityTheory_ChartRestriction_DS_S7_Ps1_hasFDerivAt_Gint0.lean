-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_Gint0
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.Ps1.hasFDerivAt_Gint0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:51.919286+00:00
-- url     : https://prove2.me/theorems/d718f5f6-2193-47ae-b0a0-0dcb4ef3a81c
-- title:
--   Ps1: has FDeriv At Gint0
-- statement:
--   The Ps1 construction uses the has FDeriv At Gint0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L139-L149

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.Ps1.hasFDerivAt_Gint0 (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε)
    (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) :
    HasFDerivAt (fun y : 𝕄 => Gint T μ y k)
      (((fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)).comp (conjCLM (toMK k⁻¹) (toMK k))).smulRight
        (T.op k * projW T * T.op k⁻¹)) x := by sorry
