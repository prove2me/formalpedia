-- Prove2me | Theorems.Thm_PI_PolynomialProperness_herm_sum_left
-- name    : PI.PolynomialProperness.herm_sum_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:18:04.130904+00:00
-- url     : https://prove2.me/theorems/ca3d0aba-0c29-4f8e-a68e-a2413e62839b
-- title:
--   Polynomial Properness: herm sum left
-- statement:
--   The Polynomial Properness construction uses the herm sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/NsqMulVecLe.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/NsqMulVecLe.lean#L85-L91

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

theorem PI.PolynomialProperness.herm_sum_left {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (u : ι → ℂ)
    (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    herm H (∑ c, u c • x c) y = ∑ c, u c * herm H (x c) y := by sorry
