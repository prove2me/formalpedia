-- Prove2me | Theorems.Thm_PI_PolynomialProperness_real_sq_bound
-- name    : PI.PolynomialProperness.real_sq_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:58:29.121043+00:00
-- url     : https://prove2.me/theorems/bd819c46-55dd-427c-a51a-74053f3b0a68
-- title:
--   Polynomial Properness: real sq bound
-- statement:
--   The Polynomial Properness construction uses the real sq bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L34-L41

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

theorem PI.PolynomialProperness.real_sq_bound {C CA m n x : ℝ} {e : ℕ} (hm : 0 ≤ m) (hmx : m ≤ CA * x ^ e) (hx : 1 ≤ x)
    (hn : n ≤ C * m ^ 2) : n ≤ |C| * CA ^ 2 * x ^ (2 * e) := by sorry
