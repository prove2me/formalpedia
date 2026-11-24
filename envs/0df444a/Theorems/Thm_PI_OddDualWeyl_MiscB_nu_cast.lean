-- Prove2me | Theorems.Thm_PI_OddDualWeyl_MiscB_nu_cast
-- name    : PI.OddDualWeyl.MiscB.nu_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:58.387908+00:00
-- url     : https://prove2.me/theorems/c0854685-689f-4f3e-9f8b-a240749b50a5
-- title:
--   Misc B: nu cast
-- statement:
--   The Misc B construction uses the nu cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/DegreeBalance.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/DegreeBalance.lean#L51-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DegreeBalance
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
open PI.OddDualWeyl.MiscB
variable {m : ℕ} {lam : Fin (m + 1) → ℤ}

theorem PI.OddDualWeyl.MiscB.nu_cast (hl : Antitone lam) (t : Fin (m + 1)) : (nuOf lam t : ℤ) = lam t - lam (Fin.last m) := by sorry
