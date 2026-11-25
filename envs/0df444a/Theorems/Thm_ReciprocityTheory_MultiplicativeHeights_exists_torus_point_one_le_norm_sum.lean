-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_torus_point_one_le_norm_sum
-- name    : ReciprocityTheory.MultiplicativeHeights.exists_torus_point_one_le_norm_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:41.305171+00:00
-- url     : https://prove2.me/theorems/e21edbdb-4b78-4c6c-8717-f32db9de35c3
-- title:
--   Multiplicative Heights: exists torus point one le norm sum
-- statement:
--   The Multiplicative Heights construction uses the exists torus point one le norm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean#L73-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean#L73-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.exists_torus_point_one_le_norm_sum {K : Type*} [NormedField K] [IsUltrametricDist K]
    (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) {n : ℕ}
    (F : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → K) (ha : ∀ χ, ‖a χ‖ ≤ 1)
    (χ₀ : Fin n → ℤ) (hχ₀ : χ₀ ∈ F) (ha₀ : ‖a χ₀‖ = 1) :
    ∃ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) ∧
      1 ≤ ‖∑ χ ∈ F, a χ * ∏ i, τ i ^ χ i‖ := by sorry
