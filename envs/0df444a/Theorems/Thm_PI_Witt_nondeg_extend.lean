-- Prove2me | Theorems.Thm_PI_Witt_nondeg_extend
-- name    : PI.Witt.nondeg_extend
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:22.331263+00:00
-- url     : https://prove2.me/theorems/d9d622ec-0d83-4464-b55a-ac9f7eac8347
-- title:
--   Witt: nondeg extend
-- statement:
--   The Witt construction uses the nondeg extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/Nondeg.lean#L8-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/Nondeg.lean#L8-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Nondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

theorem PI.Witt.nondeg_extend (h1 : OneVector) (h2 : Anisotropic) [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) :
    ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U = n →
      (∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0) →
      ∀ f : U →ₗ[K] V, (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ (∀ x : U, g x = f x) ∧
        ∀ z, (∀ u : U, B (u : V) z = 0) → (∀ u : U, B (f u) z = 0) → g z = z := by sorry
