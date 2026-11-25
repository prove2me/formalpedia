-- Prove2me | Theorems.Thm_PI_PolynomialProperness_ut_det
-- name    : PI.PolynomialProperness.ut_det
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:54.882245+00:00
-- url     : https://prove2.me/theorems/3c70a03e-f31e-4aaa-8a84-a209343586f0
-- title:
--   Polynomial Properness: ut det
-- statement:
--   The Polynomial Properness construction uses the ut det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L26-L28

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

theorem PI.PolynomialProperness.ut_det {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v.det = 1 := by sorry
