-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_symm_nodal
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_symm_nodal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:38.707855+00:00
-- url     : https://prove2.me/theorems/09e66fb2-90ac-485f-bcb4-34c0424b1cd3
-- title:
--   DS: dc symm nodal
-- statement:
--   The DS construction uses the dc symm nodal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L173-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L173-L212

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
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {S W : Submodule ℂ Y}
  {Q : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ}

theorem ReciprocityTheory.ChartRestriction.DS.dc_symm_nodal (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) (hTS : ∀ f ∈ S, T f ∈ S) (hWS : W ≤ S)
    (hW : FiniteDimensional ℂ W) (hTW : ∀ f ∈ W, T f ∈ W) :
    ∃ B : Finset ℝ, ∀ w ∈ W, aeval T (Lagrange.nodal (dc_cplxPts B) id) w = 0 := by sorry
