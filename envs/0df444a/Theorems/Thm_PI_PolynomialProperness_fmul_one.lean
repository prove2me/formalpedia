-- Prove2me | Theorems.Thm_PI_PolynomialProperness_fmul_one
-- name    : PI.PolynomialProperness.fmul_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:41.336651+00:00
-- url     : https://prove2.me/theorems/a6a7f145-ad87-4b13-9870-cffbad5d200e
-- title:
--   Polynomial Properness: fmul one
-- statement:
--   The Polynomial Properness construction uses the fmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L10-L12

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness

theorem PI.PolynomialProperness.fmul_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) :
    fmul k r z 1 b = fvec k r z b := by sorry
