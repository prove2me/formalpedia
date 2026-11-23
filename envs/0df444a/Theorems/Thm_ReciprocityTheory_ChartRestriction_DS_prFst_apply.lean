-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.prFst_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:45:07.370825+00:00
-- url     : https://prove2.me/theorems/b8f68cfa-b162-454b-9e3e-7581146bfcca
-- title:
--   DS: pr Fst apply
-- statement:
--   The DS construction uses the pr Fst apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean#L57-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

theorem ReciprocityTheory.ChartRestriction.DS.prFst_apply (x : WithLp 2 (M₁ × M₂)) : prFst x = (WithLp.ofLp x).1 := by sorry

attribute [defeq] ReciprocityTheory.ChartRestriction.DS.prFst_apply
