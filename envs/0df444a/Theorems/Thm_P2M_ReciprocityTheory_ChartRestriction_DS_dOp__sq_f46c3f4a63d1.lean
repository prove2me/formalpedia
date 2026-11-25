-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_dOp__sq_f46c3f4a63d1
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_dOp__sq_f46c3f4a63d1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:12:21.334813+00:00
-- url     : https://prove2.me/theorems/42d9532b-403c-443c-bf66-ba42db0f5c30
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS d Op  sq f46c3f4a63d1: P2 M Reciprocity Theory Chart Restriction DS d Op  sq f46c3f4a63d1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS d Op  sq f46c3f4a63d1 construction uses the P2 M Reciprocity Theory Chart Restriction DS d Op  sq f46c3f4a63d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L246-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L246-L264

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem P2M_ReciprocityTheory_ChartRestriction_DS_dOp__sq_f46c3f4a63d1 {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) : dOp' ε E cm * dOp' ε E cm = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«dOp'_sq» := P2M_ReciprocityTheory_ChartRestriction_DS_dOp__sq_f46c3f4a63d1
