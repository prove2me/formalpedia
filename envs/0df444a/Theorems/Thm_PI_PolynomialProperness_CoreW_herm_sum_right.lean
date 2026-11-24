-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sum_right
-- name    : PI.PolynomialProperness.CoreW.herm_sum_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:18:05.93319+00:00
-- url     : https://prove2.me/theorems/f16f8a73-39cf-445e-afe8-3e1e7fe5cc36
-- title:
--   Core W: herm sum right
-- statement:
--   The Core W construction uses the herm sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L106-L108

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

theorem PI.PolynomialProperness.CoreW.herm_sum_right (hH : Hᴴ = H) {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ i, f i) = ∑ i, herm H v (f i) := by sorry
