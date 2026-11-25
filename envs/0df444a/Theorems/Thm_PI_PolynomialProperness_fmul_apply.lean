-- Prove2me | Theorems.Thm_PI_PolynomialProperness_fmul_apply
-- name    : PI.PolynomialProperness.fmul_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:02.633522+00:00
-- url     : https://prove2.me/theorems/042b193c-dbd6-50a6-819f-5a31a5045a61
-- title:
--   Polynomial Properness: fmul apply
-- statement:
--   The Polynomial Properness construction uses the fmul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/NsqMulVecLe.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/NsqMulVecLe.lean#L62-L67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
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

theorem PI.PolynomialProperness.fmul_apply (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    fmul k r z c b i = ∑ a, c a b * fvec k r z a i := by sorry
