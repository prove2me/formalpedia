-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_map_noncompactLayer_le_sup
-- name    : ReciprocityTheory.ChartRestriction.DS.map_noncompactLayer_le_sup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:08.688154+00:00
-- url     : https://prove2.me/theorems/bc2131f4-760d-5017-acb1-e012f843e28b
-- title:
--   DS: map noncompact Layer le sup
-- statement:
--   The DS construction uses the map noncompact Layer le sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L243-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L243-L272

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.map_noncompactLayer_le_sup : ∀ (k : ℕ) (a b : Fin n), ε a ≠ ε b →
    (layer ε E V k).map (E a b) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1))
  := by sorry
