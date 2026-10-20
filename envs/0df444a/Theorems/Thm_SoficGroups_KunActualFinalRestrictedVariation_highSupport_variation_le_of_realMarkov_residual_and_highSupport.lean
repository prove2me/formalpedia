-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_highSupport_variation_le_of_realMarkov_residual_and_highSupport
-- name    : SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual_and_highSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/a3c2cd99-1359-4fb9-8a51-7c5084e9fe12
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual_and_highSupport
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual_and_highSupport
    {V ι : Type*} [Fintype V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (α η b : ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ))
    (hhigh :
      ((Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) ≤
          3 * (T.card : ℝ))
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ (T.card : ℝ))
    (hresidual :
      Real.sqrt (∑ x : V,
        (realMarkov σ f x - f x) ^ 2) ≤ η * b)
    (hsmall :
      486 * (Fintype.card ι : ℝ) ^ 2 * η ≤ 4 * α ^ 2) :
    9 * (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ≤ 2 * α * (T.card : ℝ) := by sorry
