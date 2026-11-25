-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_projection_identities
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.fixedUnitary_projection_identities
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:21.410219+00:00
-- url     : https://prove2.me/theorems/23fa7d4a-8c3e-4439-b909-740aed867cd7
-- title:
--   Base0: fixed Unitary projection identities
-- statement:
--   The Base0 construction uses the fixed Unitary projection identities property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L51-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L51-L80

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.fixedUnitary_projection_identities {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) :
    hᴴ * h = 1 ∧ h * Pk k = Pk k ∧ hᴴ * Pk k = Pk k ∧ Pk k * h = Pk k := by sorry
