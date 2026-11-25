-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d__e57617b1b86e
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d__e57617b1b86e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:12:17.091068+00:00
-- url     : https://prove2.me/theorems/fc5cc200-3e04-5cc8-83ad-17139c540ba9
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS car Kinv term d  e57617b1b86e: P2 M Reciprocity Theory Chart Restriction DS car Kinv term d  e57617b1b86e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS car Kinv term d  e57617b1b86e construction uses the P2 M Reciprocity Theory Chart Restriction DS car Kinv term d  e57617b1b86e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L111-L117

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d__e57617b1b86e {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E i c * cm i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E i c * cm i c) =
      ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
        E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«carKinv_term_d'» := P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d__e57617b1b86e
