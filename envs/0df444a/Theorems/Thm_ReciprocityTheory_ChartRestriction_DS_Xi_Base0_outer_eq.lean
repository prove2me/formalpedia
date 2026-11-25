-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_outer_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.outer_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:00.557577+00:00
-- url     : https://prove2.me/theorems/c901c64b-b773-4f55-b6f4-6b0e3426885f
-- title:
--   Base0: outer eq
-- statement:
--   The Base0 construction uses the outer eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L174-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L174-L190

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.outer_eq (hk : 1 ≤ k) {h' : Mat k 0} (hh : h' ∈ U0 k) (g : Mat k 0) :
    ‖((g * h') *ᵥ phiV' k 0 0) (iK k)‖ = (Real.sqrt 2)⁻¹ *
      ‖(h'ᴴ *ᵥ (fun j => star (g (iK k) j))) (iW k) + -star (g (iK k) (iK k))‖ := by sorry
