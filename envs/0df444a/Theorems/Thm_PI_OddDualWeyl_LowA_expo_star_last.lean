-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_expo_star_last
-- name    : PI.OddDualWeyl.LowA.expo_star_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:05.346463+00:00
-- url     : https://prove2.me/theorems/e890868d-39b5-410b-93ee-af91cf8f220c
-- title:
--   Low A: expo star last
-- statement:
--   The Low A construction uses the expo star last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L46-L49

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

theorem PI.OddDualWeyl.LowA.expo_star_last {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf (lamStar lam) (Fin.last m) - nuNext (nuOf (lamStar lam)) (Fin.last m) = 0 := by sorry
