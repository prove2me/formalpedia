-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_pw_mem
-- name    : PI.OddDualWeyl.Low.pw_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:29.733649+00:00
-- url     : https://prove2.me/theorems/0f74be18-dfff-44ef-908e-aa4ba40f279d
-- title:
--   Low: pw mem
-- statement:
--   The Low construction uses the pw mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L244-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L244-L255

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.Low.pw_mem {n : ℕ} (ν : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    pw R σ ν ∈ weyl R (n + 1) (n + 1) le_rfl ν := by sorry
