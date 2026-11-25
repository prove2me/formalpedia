-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_adj_inv
-- name    : PI.OddDualWeyl.Red.adj_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:38.283366+00:00
-- url     : https://prove2.me/theorems/b54aa148-f368-5f2e-b01c-0283bc51852b
-- title:
--   Red: adj inv
-- statement:
--   The Red construction uses the adj inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L194-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L194-L199

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
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
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
variable {K : Type*} [Field K] {k : ℕ}

theorem PI.OddDualWeyl.Red.adj_inv (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) : (g⁻¹).adjugate = (g.det)⁻¹ • g := by sorry
