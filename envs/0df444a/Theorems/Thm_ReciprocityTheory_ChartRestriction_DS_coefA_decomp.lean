-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_decomp
-- name    : ReciprocityTheory.ChartRestriction.DS.coefA_decomp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:49:02.819556+00:00
-- url     : https://prove2.me/theorems/a1bd71c8-983f-41c1-9116-c043a5503630
-- title:
--   DS: coef A decomp
-- statement:
--   The DS construction uses the coef A decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L13-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean#L13-L34

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

theorem ReciprocityTheory.ChartRestriction.DS.coefA_decomp {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {F : Submodule ℂ X} (hFd : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, T x ∈ F) {y : X} (hy : y ∈ F) :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ F ∧ T (b i) = (θ i : ℂ) • b i := by sorry
