-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inner_map_map__a3d9c3698dd1
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inner_map_map__a3d9c3698dd1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:20.629824+00:00
-- url     : https://prove2.me/theorems/a698b2ab-9ae7-4f53-80e5-6492ef7c998f
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Unitary Group Of Form inner map map  a3d9c3698dd1: P2 M Reciprocity Theory Chart Restriction DS Unitary Group Of Form inner map map  a3d9c3698dd1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Unitary Group Of Form inner map map  a3d9c3698dd1 construction uses the P2 M Reciprocity Theory Chart Restriction DS Unitary Group Of Form inner map map  a3d9c3698dd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L123-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
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
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inner_map_map__a3d9c3698dd1 (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«UnitaryGroupOfForm».«inner_map_map'» := P2M_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inner_map_map__a3d9c3698dd1
