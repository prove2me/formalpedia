-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Jac_jacobi
-- name    : PI.OddDualWeyl.Jac.jacobi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:58.434805+00:00
-- url     : https://prove2.me/theorems/e578fd3d-e4b5-47f0-8a25-f3a80b9ee7af
-- title:
--   Jac: jacobi
-- statement:
--   The Jac construction uses the jacobi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean#L80-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean#L80-L101

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

theorem PI.OddDualWeyl.Jac.jacobi {R : Type*} [CommRing R] {k : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty n] (eI eJ : m ⊕ n ≃ Fin k)
    (A : Matrix (Fin k) (Fin k) R) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by sorry
