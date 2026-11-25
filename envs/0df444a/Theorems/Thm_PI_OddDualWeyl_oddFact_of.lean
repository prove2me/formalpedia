-- Prove2me | Theorems.Thm_PI_OddDualWeyl_oddFact_of
-- name    : PI.OddDualWeyl.oddFact_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:41.642553+00:00
-- url     : https://prove2.me/theorems/3426633b-57ae-570d-ae07-96ab9ebc23f6
-- title:
--   Odd Dual Weyl: odd Fact of
-- statement:
--   The Odd Dual Weyl construction uses the odd Fact of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L261-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L261-L276

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
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
open PI PI.OddDualWeyl
variable {K : Type} [Field K]

theorem PI.OddDualWeyl.oddFact_of (hC1 : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam := by sorry
