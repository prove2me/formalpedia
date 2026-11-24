-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Uniq_mul_P
-- name    : PI.OddDualWeyl.Uniq.mul_P
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:48.059555+00:00
-- url     : https://prove2.me/theorems/fa02efe7-36e2-46ec-9c11-e53b0f666ce1
-- title:
--   Uniq: mul P
-- statement:
--   The Uniq construction uses the mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
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
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
variable {Rg : Type*} [CommRing Rg] {k : ℕ}

theorem PI.OddDualWeyl.Uniq.mul_P (B : Matrix (Fin k) (Fin k) Rg) : B * P Rg k = Matrix.of fun i j => B i (Fin.rev j) := by sorry
