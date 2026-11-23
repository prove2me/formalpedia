-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_eq_zero_of_eigen_not_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_eq_zero_of_eigen_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:32.506672+00:00
-- url     : https://prove2.me/theorems/78c7e147-5c5b-4ebf-9f4f-3c04a8cefb13
-- title:
--   DS: dc eq zero of eigen not mem
-- statement:
--   The DS construction uses the dc eq zero of eigen not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L53-L59

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_eq_zero_of_eigen_not_mem (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0)
    {z : ℂ} (hz : z ∉ dc_cplxPts B) {f : Y} (hf : f ∈ S) (he : T f = z • f) : f = 0 := by sorry
