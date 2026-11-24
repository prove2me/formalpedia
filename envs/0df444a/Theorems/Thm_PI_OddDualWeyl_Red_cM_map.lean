-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_cM_map
-- name    : PI.OddDualWeyl.Red.cM_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:00.034681+00:00
-- url     : https://prove2.me/theorems/944ba0c2-d64e-458a-a528-f1618b92a030
-- title:
--   Red: c M map
-- statement:
--   The Red construction uses the c M map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L51-L54

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

theorem PI.OddDualWeyl.Red.cM_map (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (g : Matrix (Fin k) (Fin k) R) :
    (cM g).map (sbs A) = cM g := by sorry
