-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_hw_mem
-- name    : PI.OddDualWeyl.Low.hw_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:53.158075+00:00
-- url     : https://prove2.me/theorems/7714b429-4982-43ad-9d7d-151a4e20b043
-- title:
--   Low: hw mem
-- statement:
--   The Low construction uses the hw mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L122-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L122-L123

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

theorem PI.OddDualWeyl.Low.hw_mem {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : hw R hn ν ∈ weyl R r n hn ν := by sorry
