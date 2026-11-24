-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_expo_castSucc
-- name    : PI.OddDualWeyl.LowA.expo_castSucc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:53.011904+00:00
-- url     : https://prove2.me/theorems/f3b72b8b-3fde-4f6c-8928-bcd1b265657c
-- title:
--   Low A: expo cast Succ
-- statement:
--   The Low A construction uses the expo cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L35-L44

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

theorem PI.OddDualWeyl.LowA.expo_castSucc {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (s : Fin m) :
    nuOf (lamStar lam) s.castSucc - nuNext (nuOf (lamStar lam)) s.castSucc =
      nuOf lam s.rev.castSucc - nuNext (nuOf lam) s.rev.castSucc := by sorry
