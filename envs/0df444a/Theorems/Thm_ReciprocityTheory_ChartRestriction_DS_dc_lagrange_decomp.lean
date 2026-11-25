-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_lagrange_decomp
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_lagrange_decomp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:59.819882+00:00
-- url     : https://prove2.me/theorems/07052286-8e59-4afe-99d8-d57abacd9ac8
-- title:
--   DS: dc lagrange decomp
-- statement:
--   The DS construction uses the dc lagrange decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L61-L81

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_lagrange_decomp (hT : ∀ f ∈ S, T f ∈ S)
    (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) :
    ∀ f ∈ S, ∃ fb : ℝ → Y, (∀ b, fb b ∈ S ∧ T (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b := by sorry
