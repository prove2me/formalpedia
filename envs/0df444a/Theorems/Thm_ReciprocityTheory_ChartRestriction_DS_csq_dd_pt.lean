-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_dd_pt
-- name    : ReciprocityTheory.ChartRestriction.DS.csq_dd_pt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:45.469446+00:00
-- url     : https://prove2.me/theorems/48287d49-9442-5fdf-a474-d53ea626c2f7
-- title:
--   DS: csq dd pt
-- statement:
--   The DS construction uses the csq dd pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CsqDdPt.lean#L10-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CsqDdPt.lean#L10-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
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

theorem ReciprocityTheory.ChartRestriction.DS.csq_dd_pt {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (i a j b : Fin n) :
    E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      (if i = j then E a b * (cp i a * cm j b) else 0) - (if b = a then E j i * (cp i a * cm j b) else 0) +
        (if b = a then (if j = i then E i a * E a i else 0) else 0) := by sorry
