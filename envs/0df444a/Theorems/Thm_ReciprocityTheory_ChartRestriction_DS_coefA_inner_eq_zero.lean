-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_inner_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.coefA_inner_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:26.968798+00:00
-- url     : https://prove2.me/theorems/a20f142d-2f35-4d6d-88a3-b56e4546678d
-- title:
--   DS: coef A inner eq zero
-- statement:
--   The DS construction uses the coef A inner eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L36-L43

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

theorem ReciprocityTheory.ChartRestriction.DS.coefA_inner_eq_zero {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {u v : X} {α β : ℝ} (hu : T u = (α : ℂ) • u) (hv : T v = (β : ℂ) • v) (hne : α ≠ β) :
    inner ℂ u v = 0 := by sorry
