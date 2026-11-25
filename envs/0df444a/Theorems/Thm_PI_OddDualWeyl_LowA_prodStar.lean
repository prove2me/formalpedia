-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_prodStar
-- name    : PI.OddDualWeyl.LowA.prodStar
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:40.801158+00:00
-- url     : https://prove2.me/theorems/e76a19f5-e1d2-4680-90d5-b47ffb54e881
-- title:
--   Low A: prod Star
-- statement:
--   The Low A construction uses the prod Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L158-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L158-L170

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.LowA.prodStar {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1)))
    (D : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (u : Fin (m + 1) → R)
    (hu : ∀ s, u s = 1 ∨ u s = -1)
    (hD : ∀ s : Fin (m + 1), D s = C (u s) * (genM R (m + 1)).det ^ s.val *
      pMinor R σ (m + 1 - 1 - s.val) (by omega)) :
    ∃ U : R, (U = 1 ∨ U = -1) ∧
      ∏ s, D s ^ (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) =
        C U * (genM R (m + 1)).det ^ expM lam * pw R σ (nuOf lam) := by sorry
