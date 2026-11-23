-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:42:19.298797+00:00
-- url     : https://prove2.me/theorems/afdc3510-4b06-4d66-967f-93a103c1fc9b
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS coord apply  ef209eafcd1f: P2 M Reciprocity Theory Chart Restriction DS coord apply  ef209eafcd1f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS coord apply  ef209eafcd1f construction uses the P2 M Reciprocity Theory Chart Restriction DS coord apply  ef209eafcd1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L17-L18

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f (k : ℕ) (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ F = F κ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«coord_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f
