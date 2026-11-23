-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_smul__ee45d6d95b18
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_actM_smul__ee45d6d95b18
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:53.727291+00:00
-- url     : https://prove2.me/theorems/b8a47437-36e1-4464-9bbc-c4d6d82d4301
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS act M smul  ee45d6d95b18: P2 M Reciprocity Theory Chart Restriction DS act M smul  ee45d6d95b18
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS act M smul  ee45d6d95b18 construction uses the P2 M Reciprocity Theory Chart Restriction DS act M smul  ee45d6d95b18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L21-L23

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_actM_smul__ee45d6d95b18 {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«actM_smul'» := P2M_ReciprocityTheory_ChartRestriction_DS_actM_smul__ee45d6d95b18
