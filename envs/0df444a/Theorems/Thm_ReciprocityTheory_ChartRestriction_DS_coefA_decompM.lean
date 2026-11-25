-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_decompM
-- name    : ReciprocityTheory.ChartRestriction.DS.coefA_decompM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:36.858089+00:00
-- url     : https://prove2.me/theorems/313a38c1-2acf-4f36-889d-5bb9e5f2df93
-- title:
--   DS: coef A decomp M
-- statement:
--   The DS construction uses the coef A decomp M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L55-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

theorem ReciprocityTheory.ChartRestriction.DS.coefA_decompM {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') {y : X} (hy : y ∈ M') :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ M' ∧ T (b i) = (θ i : ℂ) • b i := by sorry
