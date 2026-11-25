-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_good_X_mul_C
-- name    : PI.OddDualWeyl.Hom.good_X_mul_C
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:07.89108+00:00
-- url     : https://prove2.me/theorems/de6544b5-26db-447f-86df-13ddeaa1f5eb
-- title:
--   Hom: good X mul C
-- statement:
--   The Hom construction uses the good X mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L45-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
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
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}

theorem PI.OddDualWeyl.Hom.good_X_mul_C {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R}
    (hc : IsWeightedHomogeneous wt c (d + δ)) : Good wt δ d (Polynomial.X * Polynomial.C c) := by sorry
