-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Jac_det_sub
-- name    : PI.OddDualWeyl.Jac.det_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:29.941865+00:00
-- url     : https://prove2.me/theorems/dd68bde8-ec10-4ac3-b944-97194727a7a6
-- title:
--   Jac: det sub
-- statement:
--   The Jac construction uses the det sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean#L29-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity
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
open PI PI.OddDualWeyl PI.OddDualWeyl.Jac

theorem PI.OddDualWeyl.Jac.det_sub {R : Type*} [CommRing R] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eI eJ : ι ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) :
    (A.submatrix eI eJ).det = ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det := by sorry
