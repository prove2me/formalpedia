-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sum_left
-- name    : PI.PolynomialProperness.CoreW.herm_sum_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:19:14.84241+00:00
-- url     : https://prove2.me/theorems/a2151476-d4f5-44c2-a5d9-47aa6b9f0a82
-- title:
--   Core W: herm sum left
-- statement:
--   The Core W construction uses the herm sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L94-L96

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

theorem PI.PolynomialProperness.CoreW.herm_sum_left {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i, f i) w = ∑ i, herm H (f i) w := by sorry
