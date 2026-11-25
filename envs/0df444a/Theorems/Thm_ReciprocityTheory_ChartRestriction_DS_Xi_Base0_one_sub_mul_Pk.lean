-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_one_sub_mul_Pk
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.one_sub_mul_Pk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:51.664952+00:00
-- url     : https://prove2.me/theorems/3d96b0e4-59cd-5081-a6ba-bd9df3b2d465
-- title:
--   Base0: one sub mul Pk
-- statement:
--   The Base0 construction uses the one sub mul Pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean#L47-L49

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.one_sub_mul_Pk (k : ℕ) : (1 - 2 • Pk k) * Pk k = -Pk k := by sorry
