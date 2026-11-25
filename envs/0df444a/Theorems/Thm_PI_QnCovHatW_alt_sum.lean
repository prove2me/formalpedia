-- Prove2me | Theorems.Thm_PI_QnCovHatW_alt_sum
-- name    : PI.QnCovHatW.alt_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:36:36.237992+00:00
-- url     : https://prove2.me/theorems/848c7108-d9d9-4664-b3fb-ec7d1fb20e01
-- title:
--   Qn Cov Hat W: alt sum
-- statement:
--   The Qn Cov Hat W construction uses the alt sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/InjDecomp.lean#L39-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatDecomposition/InjDecomp.lean#L39-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PI PI.QnCovHatW

theorem PI.QnCovHatW.alt_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ}
    (g : (Fin m → Fin (m + 1)) → M)
    (hskew : ∀ c (σ : Equiv.Perm (Fin m)), g (c ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • g c)
    (hzero : ∀ c, ¬ Function.Injective c → g c = 0)
    (w : (Fin m → Fin (m + 1)) → ℂ) :
    ∑ c, w c • g c =
      ∑ i : Fin (m + 1),
        (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * w (i.succAbove ∘ σ)) • g i.succAbove := by sorry
