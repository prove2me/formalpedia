-- Prove2me | Theorems.Thm_PI_OddDualWeyl_core1
-- name    : PI.OddDualWeyl.core1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:57.593305+00:00
-- url     : https://prove2.me/theorems/87d611e5-955f-4cc0-8489-38a69e9de24b
-- title:
--   Odd Dual Weyl: core1
-- statement:
--   The Odd Dual Weyl construction uses the core1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L77-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L77-L128

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

theorem PI.OddDualWeyl.core1 (h1 : W1) (hMh : MHhw) (hMd : MHdiv) (hD : Diag) (hL : LowMem) (h4 : W4hw)
    (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ) (hl : Antitone lam) :
    ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      Rel R (m + 1) (expM lam) f f' := by sorry
