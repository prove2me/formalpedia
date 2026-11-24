-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_star_H_dot
-- name    : PI.PolynomialProperness.CoreW.star_H_dot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:51.396645+00:00
-- url     : https://prove2.me/theorems/493a280f-7467-4511-b839-57a0a611bcb8
-- title:
--   Core W: star H dot
-- statement:
--   The Core W construction uses the star H dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L53-L56

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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem PI.PolynomialProperness.CoreW.star_H_dot (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) :
    star (H *ᵥ v) ⬝ᵥ (H *ᵥ v) = star v ⬝ᵥ v := by sorry
