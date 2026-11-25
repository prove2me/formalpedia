-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Uniq_dualSub_dualM
-- name    : PI.OddDualWeyl.Uniq.dualSub_dualM
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:16.743243+00:00
-- url     : https://prove2.me/theorems/731c33e5-863f-4951-8cde-e6258cca0ddd
-- title:
--   Uniq: dual Sub dual M
-- statement:
--   The Uniq construction uses the dual Sub dual M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean#L39-L52

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

theorem PI.OddDualWeyl.Uniq.dualSub_dualM (hk : k ≠ 1) (i j : Fin k) :
    dualSub Rg k (dualM Rg k i j) = (P _ k).det * (genM Rg k).det ^ (k - 2) * X (i, j) := by sorry
