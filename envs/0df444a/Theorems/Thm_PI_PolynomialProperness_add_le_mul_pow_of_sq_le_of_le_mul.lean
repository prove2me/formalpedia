-- Prove2me | Theorems.Thm_PI_PolynomialProperness_add_le_mul_pow_of_sq_le_of_le_mul
-- name    : PI.PolynomialProperness.add_le_mul_pow_of_sq_le_of_le_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:17:44.658008+00:00
-- url     : https://prove2.me/theorems/b1977365-873a-587b-bff6-78e3f8e057a3
-- title:
--   Polynomial Properness: add le mul pow of sq le of le mul
-- statement:
--   The Polynomial Properness construction uses the add le mul pow of sq le of le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L43-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L43-L70

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

theorem PI.PolynomialProperness.add_le_mul_pow_of_sq_le_of_le_mul {Cc D a s sp x : ℝ} {e N : ℕ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hs1 : 1 ≤ s) (hx : 1 ≤ x)
    (hs : s ^ 2 ≤ Cc * (1 + D * x ^ (2 * e + 2)) ^ 2) (hsp : sp ≤ a * s * x) (hN : 4 * e + 5 ≤ N) :
    s + sp ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N := by sorry
