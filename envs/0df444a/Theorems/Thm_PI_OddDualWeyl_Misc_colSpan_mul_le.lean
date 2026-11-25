-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Misc_colSpan_mul_le
-- name    : PI.OddDualWeyl.Misc.colSpan_mul_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:15:00.514954+00:00
-- url     : https://prove2.me/theorems/fbd0cbb4-09ed-5211-9f66-5728f00fb8e8
-- title:
--   Misc: col Span mul le
-- statement:
--   The Misc construction uses the col Span mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/ExistsEqMulOfColumnSpanLe.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/ExistsEqMulOfColumnSpanLe.lean#L40-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe
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
open PI.OddDualWeyl.Misc
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem PI.OddDualWeyl.Misc.colSpan_mul_le {n : ℕ} (h' : Matrix (Fin n) (Fin n) K) (v : Matrix (Fin n) (Fin n) O) :
    colSpan O (h' * v.map (algebraMap O K)) ≤ colSpan O h' := by sorry
