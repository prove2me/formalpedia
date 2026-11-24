-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_iW_ne_iK
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.iW_ne_iK
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:12:45.453572+00:00
-- url     : https://prove2.me/theorems/545d1753-8933-4fd6-9898-6ead2ec640fc
-- title:
--   Base0: i W ne i K
-- statement:
--   The Base0 construction uses the i W ne i K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L20-L24

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.iW_ne_iK {k : ℕ} (hk : 1 ≤ k) : iW k ≠ iK k := by sorry
