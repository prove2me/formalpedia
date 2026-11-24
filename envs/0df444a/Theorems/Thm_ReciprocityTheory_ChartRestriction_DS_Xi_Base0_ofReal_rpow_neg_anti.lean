-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_ofReal_rpow_neg_anti
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.ofReal_rpow_neg_anti
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:54:57.371783+00:00
-- url     : https://prove2.me/theorems/09a513e2-e2f5-46d4-8e10-2239ff2fdb46
-- title:
--   Base0: of Real rpow neg anti
-- statement:
--   The Base0 construction uses the of Real rpow neg anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L19-L22

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.ofReal_rpow_neg_anti {a b s : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) :
    ENNReal.ofReal b ^ (-s) ≤ ENNReal.ofReal a ^ (-s) := by sorry
