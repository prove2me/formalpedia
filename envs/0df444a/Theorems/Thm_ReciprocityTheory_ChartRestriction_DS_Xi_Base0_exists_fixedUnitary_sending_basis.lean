-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_exists_fixedUnitary_sending_basis
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.exists_fixedUnitary_sending_basis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:42.787057+00:00
-- url     : https://prove2.me/theorems/0874d7fe-a410-5e01-90f3-73031afb0b25
-- title:
--   Base0: exists fixed Unitary sending basis
-- statement:
--   The Base0 construction uses the exists fixed Unitary sending basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L123-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L123-L277

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.exists_fixedUnitary_sending_basis {k : ℕ} (hk : 1 ≤ k) (u : Fin (2 * 0 + k + 1) → ℂ) (hu0 : u (iK k) = 0)
    (hu1 : star u ⬝ᵥ u = 1) : ∃ R ∈ U0 k, R *ᵥ bvec (iW k) = u := by sorry
