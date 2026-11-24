-- Prove2me | Theorems.Thm_PI_OddDualWeyl_invT_invT
-- name    : PI.OddDualWeyl.invT_invT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:12.538487+00:00
-- url     : https://prove2.me/theorems/2eb2c500-27e5-4d0d-b237-ec24bff4cd32
-- title:
--   Odd Dual Weyl: inv T inv T
-- statement:
--   The Odd Dual Weyl construction uses the inv T inv T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L147-L149

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

theorem PI.OddDualWeyl.invT_invT {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : (((g⁻¹)ᵀ)⁻¹)ᵀ = g := by sorry
