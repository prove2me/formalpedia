-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lift_khw
-- name    : ReciprocityTheory.ChartRestriction.DS.lift_khw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:46.899234+00:00
-- url     : https://prove2.me/theorems/ae6fa9b6-8237-45ee-801d-03138ccaabb4
-- title:
--   DS: lift khw
-- statement:
--   The DS construction uses the lift khw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KUnitB.lean#L137-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KUnitB.lean#L137-L178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
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
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.lift_khw (hU : IsKUnitary ε A) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ a b, ε a = ε b → ∀ x, f (A a b x) = B a b (f x)) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) {x₀ : X} (hx₀ : x₀ ∈ S)
    {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (f x₀)) :
    ∃ x ∈ S, (∀ z ∈ S, f z = 0 → inner ℂ z x = 0) ∧ IsKHWVec ε A μ x ∧ f x = f x₀ := by sorry
