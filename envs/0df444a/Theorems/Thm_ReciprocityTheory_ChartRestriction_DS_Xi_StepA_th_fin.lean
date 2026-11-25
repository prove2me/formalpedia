-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_th_fin
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.th_fin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:05.93492+00:00
-- url     : https://prove2.me/theorems/9bad2d22-aa10-57b3-a0b0-db983ef98d83
-- title:
--   Step A: th fin
-- statement:
--   The Step A construction uses the th fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkNegMp.lean#L178-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkNegMp.lean#L178-L199

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.th_fin (hB2 : InductiveHeisenbergInputs) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k) (t : Fin (1 + r' + 1) → ℝ)
    (hν : CHCond (1 + r') fun l => t l - s0N (1 + r') (k - 1) l) :
    (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) < ∞ := by sorry
