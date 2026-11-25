-- Prove2me | Theorems.Thm_PI_Witt_enlarge_step
-- name    : PI.Witt.enlarge_step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:13.90605+00:00
-- url     : https://prove2.me/theorems/24efdfda-9437-5e31-a1f1-b2dcd0406129
-- title:
--   Witt: enlarge step
-- statement:
--   The Witt construction uses the enlarge step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/EnlargeStep.lean#L34-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/EnlargeStep.lean#L34-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_EnlargeStep
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

theorem PI.Witt.enlarge_step [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hB : ∀ x y, star (B x y) = B y x) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (U : Submodule K V) (f : U →ₗ[K] V) (hinj : Function.Injective f)
    (hf : ∀ x y : U, B (f x) (f y) = B x y)
    (r : V) (hrU : r ∈ U) (hr0 : r ≠ 0) (hr : ∀ u ∈ U, B r u = 0) :
    ∃ (U' : Submodule K V) (hlt : U < U') (f' : U' →ₗ[K] V), Function.Injective f' ∧
      (∀ x y : U', B (f' x) (f' y) = B x y) ∧ ∀ u : U, f' ⟨u, hlt.le u.2⟩ = f u := by sorry
