-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ite_end_coord
-- name    : ReciprocityTheory.ChartRestriction.DS.ite_end_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:18.983354+00:00
-- url     : https://prove2.me/theorems/6e50d479-94df-4dea-9464-d237d0d4eae0
-- title:
--   DS: ite end coord
-- statement:
--   The DS construction uses the ite end coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L59-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.ite_end_coord (p : Prop) [Decidable p] (A : Module.End ℂ (Fin n → M)) (f : Fin n → M) (x : Fin n) :
    (if p then A else 0) f x = if p then A f x else 0 := by sorry
