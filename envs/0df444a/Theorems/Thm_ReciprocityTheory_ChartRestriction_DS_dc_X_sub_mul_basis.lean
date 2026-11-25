-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_X_sub_mul_basis
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_X_sub_mul_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:49:37.01751+00:00
-- url     : https://prove2.me/theorems/90ed961f-d1d4-4d6e-84d2-45c5d91fbf45
-- title:
--   DS: dc X sub mul basis
-- statement:
--   The DS construction uses the dc X sub mul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L25-L29

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_X_sub_mul_basis {s : Finset ℂ} {z : ℂ} (hz : z ∈ s) :
    (X - C z) * Lagrange.basis s id z = C (Lagrange.nodalWeight s id z) * Lagrange.nodal s id := by sorry
