-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_nuStar_apply
-- name    : PI.OddDualWeyl.LowA.nuStar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:13.833215+00:00
-- url     : https://prove2.me/theorems/bc2ca0f7-adfd-4595-9c21-ff18605ab55d
-- title:
--   Low A: nu Star apply
-- statement:
--   The Low A construction uses the nu Star apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L24-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
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
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.LowA.nuStar_apply {m : ℕ} (lam : Fin (m + 1) → ℤ) (t : Fin (m + 1)) :
    nuOf (lamStar lam) t = (lam 0 - lam t.rev).toNat := by sorry
