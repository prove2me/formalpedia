-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_tele
-- name    : PI.OddDualWeyl.LowA.tele
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:49.252094+00:00
-- url     : https://prove2.me/theorems/2e2ae5ca-a3d3-423d-93ad-a94bfb5262f0
-- title:
--   Low A: tele
-- statement:
--   The Low A construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L69-L83

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

theorem PI.OddDualWeyl.LowA.tele (G : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℤ) - 1 - j) * (G j - G (j + 1)) =
      n * G 0 - ∑ j ∈ Finset.range n, G j := by sorry
