-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_coef_bound
-- name    : PI.PolynomialProperness.CoreW.coef_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:36.357564+00:00
-- url     : https://prove2.me/theorems/2c4494ce-afd1-4c6c-8738-9589d4628318
-- title:
--   Core W: coef bound
-- statement:
--   The Core W construction uses the coef bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L158-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L158-L174

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.PolynomialProperness.CoreW.coef_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) (i : ι) :
    ‖coef H Γi p y i‖ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by sorry
