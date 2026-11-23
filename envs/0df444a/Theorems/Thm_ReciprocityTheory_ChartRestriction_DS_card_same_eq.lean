-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_card_same_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.card_same_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:11.932814+00:00
-- url     : https://prove2.me/theorems/91998ae6-dbe3-4d8c-abb9-4af45908cb86
-- title:
--   DS: card same eq
-- statement:
--   The DS construction uses the card same eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L47-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
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

theorem ReciprocityTheory.ChartRestriction.DS.card_same_eq (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = if ε a then pOf ε else qOf ε := by sorry
