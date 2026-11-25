-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_lint_lmul
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.lint_lmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:55:08.49724+00:00
-- url     : https://prove2.me/theorems/d9c6a1da-64bc-5e52-9ee4-62a1e42df032
-- title:
--   Base0: lint lmul
-- statement:
--   The Base0 construction uses the lint lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L93-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.lint_lmul {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {a : Mat k 0} (ha : a ∈ U0 k)
    {F : Mt k 0 → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x, F (lmulM a x) ∂ν = ∫⁻ x, F x ∂ν := by sorry
