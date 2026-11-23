-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_basis_eigen
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_basis_eigen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:43.643244+00:00
-- url     : https://prove2.me/theorems/82485138-019c-476c-a693-57fa0cb84b89
-- title:
--   DS: dc basis eigen
-- statement:
--   The DS construction uses the dc basis eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L44-L51

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
variable {T : Module.End ℂ Y} {S : Submodule ℂ Y} {B : Finset ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.dc_basis_eigen (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) {z : ℂ}
    (hz : z ∈ dc_cplxPts B) : ∀ f ∈ S, T (aeval T (Lagrange.basis (dc_cplxPts B) id z) f) =
      z • aeval T (Lagrange.basis (dc_cplxPts B) id z) f := by sorry
