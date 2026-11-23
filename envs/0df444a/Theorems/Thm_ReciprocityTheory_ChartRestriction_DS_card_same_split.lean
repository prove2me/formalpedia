-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_card_same_split
-- name    : ReciprocityTheory.ChartRestriction.DS.card_same_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:57.095739+00:00
-- url     : https://prove2.me/theorems/dedfc722-f40f-4f91-88b9-fb5007ab2bb8
-- title:
--   DS: card same split
-- statement:
--   The DS construction uses the card same split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L36-L45

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

theorem ReciprocityTheory.ChartRestriction.DS.card_same_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 +
      (univ.filter fun b => a < b ∧ ε b = ε a).card := by sorry
