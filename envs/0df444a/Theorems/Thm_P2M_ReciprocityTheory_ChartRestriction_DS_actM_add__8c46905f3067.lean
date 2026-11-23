-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_add__8c46905f3067
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_actM_add__8c46905f3067
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:27.97936+00:00
-- url     : https://prove2.me/theorems/86d1f842-229d-4593-bb9b-ffb5c6e5ccc1
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS act M add  8c46905f3067: P2 M Reciprocity Theory Chart Restriction DS act M add  8c46905f3067
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS act M add  8c46905f3067 construction uses the P2 M Reciprocity Theory Chart Restriction DS act M add  8c46905f3067 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L17-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_actM_add__8c46905f3067 {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«actM_add'» := P2M_ReciprocityTheory_ChartRestriction_DS_actM_add__8c46905f3067
