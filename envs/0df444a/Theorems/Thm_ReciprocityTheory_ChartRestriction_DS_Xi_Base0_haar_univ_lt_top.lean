-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_haar_univ_lt_top
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.haar_univ_lt_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:46.280092+00:00
-- url     : https://prove2.me/theorems/759523f7-77bd-4a1c-8a6e-9e8a329ac488
-- title:
--   Base0: haar univ lt top
-- statement:
--   The Base0 construction uses the haar univ lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L84-L91

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.haar_univ_lt_top (hCW : CompactW) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ν Set.univ < ∞ := by sorry
