-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_dOp__comm_diagE_7f96b23c099e
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_dOp__comm_diagE_7f96b23c099e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:12:18.876046+00:00
-- url     : https://prove2.me/theorems/680f0316-910f-44bf-b46f-2520cc77adbe
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS d Op  comm diag E 7f96b23c099e: P2 M Reciprocity Theory Chart Restriction DS d Op  comm diag E 7f96b23c099e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS d Op  comm diag E 7f96b23c099e construction uses the P2 M Reciprocity Theory Chart Restriction DS d Op  comm diag E 7f96b23c099e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L156-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L156-L192

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_dOp__comm_diagE_7f96b23c099e {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp' ε E cm * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp' ε E cm := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«dOp'_comm_diagE» := P2M_ReciprocityTheory_ChartRestriction_DS_dOp__comm_diagE_7f96b23c099e
