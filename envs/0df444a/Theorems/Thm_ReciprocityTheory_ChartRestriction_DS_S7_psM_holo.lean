-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_holo
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.psM_holo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:18.06787+00:00
-- url     : https://prove2.me/theorems/22a2c665-31f1-42dc-8569-8bb0c1bced7a
-- title:
--   S7: ps M holo
-- statement:
--   The S7 construction uses the ps M holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L250-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L250-L269

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.psM_holo {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧
      (∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) ∧
      DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
            (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by sorry
