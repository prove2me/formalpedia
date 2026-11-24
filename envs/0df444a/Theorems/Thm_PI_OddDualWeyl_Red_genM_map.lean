-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_genM_map
-- name    : PI.OddDualWeyl.Red.genM_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:36.796859+00:00
-- url     : https://prove2.me/theorems/78cca4e5-9896-4a1f-b99a-b2275ebbe286
-- title:
--   Red: gen M map
-- statement:
--   The Red construction uses the gen M map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L46-L49

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

theorem PI.OddDualWeyl.Red.genM_map (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    (genM R k).map (sbs A) = A := by sorry
