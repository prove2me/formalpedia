-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_proj_orth
-- name    : PI.PolynomialProperness.CoreW.proj_orth
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:18:00.034005+00:00
-- url     : https://prove2.me/theorems/82831939-0e44-4287-9f74-a8a271c22cb2
-- title:
--   Core W: proj orth
-- statement:
--   The Core W construction uses the proj orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L135-L138

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

theorem PI.PolynomialProperness.CoreW.proj_orth (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (y - proj H Γi p y) (p j) = 0 := by sorry
