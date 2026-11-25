-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_cInt_fin
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.cInt_fin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:49:49.160604+00:00
-- url     : https://prove2.me/theorems/54c2d432-798a-4ca7-a53c-62aee2b2900e
-- title:
--   Step A: c Int fin
-- statement:
--   The Step A construction uses the c Int fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/EIntBound.lean#L24-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/EIntBound.lean#L24-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ScaleInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergMapContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_EIntBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.cInt_fin (n : ℕ) (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 2 * (n : ℝ) + 1) :
    (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
      ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹)) < ∞ := by sorry
