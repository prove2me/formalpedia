-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_hpk_mulVec
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.hpk_mulVec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:54:26.3865+00:00
-- url     : https://prove2.me/theorems/e7a0c439-906e-45a6-9724-ef7f4115fde7
-- title:
--   Base0: hpk mul Vec
-- statement:
--   The Base0 construction uses the hpk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L23-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.hpk_mulVec (v : Fin (2 * 0 + k + 1) → ℂ) (i : Fin (2 * 0 + k + 1)) :
    (Hpk k 0 *ᵥ v) i = sg k i * v i := by sorry
