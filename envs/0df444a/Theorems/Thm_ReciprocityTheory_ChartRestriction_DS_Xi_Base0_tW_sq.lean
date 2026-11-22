-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_tW_sq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.tW_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:42.15254+00:00
-- url     : https://prove2.me/theorems/5ce0a534-22ed-403a-9dc4-eaa1b192fa20
-- title:
--   Base0: t W sq
-- statement:
--   The Base0 construction uses the t W sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HalfLeNormOneSub.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HalfLeNormOneSub.lean#L18-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.tW_sq (q : ι) (x : ι → ℂ) :
    tW q x ^ 2 = ∑ i, Complex.normSq (x i) - Complex.normSq (x q) := by sorry
