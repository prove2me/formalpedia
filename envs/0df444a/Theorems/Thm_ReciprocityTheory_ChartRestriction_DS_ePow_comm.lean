-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.ePow_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:14.311034+00:00
-- url     : https://prove2.me/theorems/e7dfa10b-7bf5-4f46-a41a-2d42c9b90aed
-- title:
--   DS: e Pow comm
-- statement:
--   The DS construction uses the e Pow comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Gelfand.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Gelfand.lean#L22-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Lemmata_MiscLemmasP_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
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

theorem ReciprocityTheory.ChartRestriction.DS.ePow_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    E a b * ePow E k c d - ePow E k c d * E a b =
      (if b = c then ePow E k a d else 0) - (if d = a then ePow E k c b else 0) := by sorry
