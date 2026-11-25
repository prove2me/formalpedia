-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_lagProj_props
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_lagProj_props
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:55.335647+00:00
-- url     : https://prove2.me/theorems/f9b18ff2-5aaa-4cbb-8e92-8beff6c1aa9b
-- title:
--   DS: dc lag Proj props
-- statement:
--   The DS construction uses the dc lag Proj props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L94-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L94-L120

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_lagProj_props (hT : ∀ f ∈ S, T f ∈ S)
    (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) (z : ℂ) :
    (∀ f ∈ S, dc_lagProj T B z (dc_lagProj T B z f) = dc_lagProj T B z f) ∧
      (∀ f ∈ S, T (dc_lagProj T B z f) = z • dc_lagProj T B z f) ∧
      (∀ f ∈ S, T f = z • f → dc_lagProj T B z f = f) ∧
      ∀ f ∈ S, ∀ z' : ℂ, z' ≠ z → T f = z' • f → dc_lagProj T B z f = 0 := by sorry
