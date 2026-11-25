-- Prove2me | Theorems.Thm_PI_OddDualWeyl_isUnit_revInv
-- name    : PI.OddDualWeyl.isUnit_revInv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:04.581504+00:00
-- url     : https://prove2.me/theorems/86444a90-1e6c-4ecf-8ba9-c9b1bde63148
-- title:
--   Odd Dual Weyl: is Unit rev Inv
-- statement:
--   The Odd Dual Weyl construction uses the is Unit rev Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L171-L179

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

theorem PI.OddDualWeyl.isUnit_revInv {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    IsUnit (revCol (z⁻¹)ᵀ).det := by sorry
