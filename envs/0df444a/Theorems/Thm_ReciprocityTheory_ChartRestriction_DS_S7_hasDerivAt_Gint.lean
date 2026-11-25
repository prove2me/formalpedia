-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hasDerivAt_Gint
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_Gint
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:16.829964+00:00
-- url     : https://prove2.me/theorems/e875e299-d071-5752-94d9-6594632a66c0
-- title:
--   S7: has Deriv At Gint
-- statement:
--   The S7 construction uses the has Deriv At Gint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DerivG.lean#L19-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DerivG.lean#L19-L115

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
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
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_Gint {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    (γ : ℝ → KG ε) (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => Gint T μ x (k * γ t))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
          (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) •
          (T.op k * projW T * T.op k⁻¹) +
        PhiM μ (toMK k⁻¹ * x * toMK k) •
          (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹)) 0 := by sorry
