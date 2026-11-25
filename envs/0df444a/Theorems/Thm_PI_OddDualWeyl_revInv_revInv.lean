-- Prove2me | Theorems.Thm_PI_OddDualWeyl_revInv_revInv
-- name    : PI.OddDualWeyl.revInv_revInv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:52.877058+00:00
-- url     : https://prove2.me/theorems/e20c1bc5-2884-4d6b-a2d7-4dfcac8a530c
-- title:
--   Odd Dual Weyl: rev Inv rev Inv
-- statement:
--   The Odd Dual Weyl construction uses the rev Inv rev Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L181-L188

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

theorem PI.OddDualWeyl.revInv_revInv {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    revCol ((revCol (z⁻¹)ᵀ)⁻¹)ᵀ = z := by sorry
