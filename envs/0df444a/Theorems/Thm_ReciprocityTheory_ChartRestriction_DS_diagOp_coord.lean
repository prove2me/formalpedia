-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_diagOp_coord
-- name    : ReciprocityTheory.ChartRestriction.DS.diagOp_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:38.836324+00:00
-- url     : https://prove2.me/theorems/28033dbd-fdeb-4770-b505-d3167509ce1c
-- title:
--   DS: diag Op coord
-- statement:
--   The DS construction uses the diag Op coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L48-L50

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

theorem ReciprocityTheory.ChartRestriction.DS.diagOp_coord (A : Module.End ℂ M) (f : Fin n → M) (c : Fin n) :
    diagOp (n := n) A f c = A (f c) := by sorry
