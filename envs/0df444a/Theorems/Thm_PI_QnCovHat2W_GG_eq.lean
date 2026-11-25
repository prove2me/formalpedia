-- Prove2me | Theorems.Thm_PI_QnCovHat2W_GG_eq
-- name    : PI.QnCovHat2W.GG_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:43.639991+00:00
-- url     : https://prove2.me/theorems/4d446bf8-657c-4d8b-89fa-cf146948725c
-- title:
--   Qn Cov Hat2 W: GG eq
-- statement:
--   The Qn Cov Hat2 W construction uses the GG eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/GGEq.lean#L32-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/GGEq.lean#L32-L80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovHat2W.GG_eq {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (hR : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) y = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (hC : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F x (y ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F β β' a a' = ((m.factorial : ℂ) * m.factorial) •
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2), ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β i * β' i' - β i' * β' i) *
            (a j * a' j' - a j' * a' j)) • F (skip2 i i') (skip2 j j')
        else 0 := by sorry
