-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_proj_right
-- name    : PI.PolynomialProperness.CoreW.herm_proj_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:36:05.270905+00:00
-- url     : https://prove2.me/theorems/751be996-cd58-5551-9dc8-8eb313c11f91
-- title:
--   Core W: herm proj right
-- statement:
--   The Core W construction uses the herm proj right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L140-L145

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

theorem PI.PolynomialProperness.CoreW.herm_proj_right (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (Γi : Matrix ι ι ℂ)
    (p : ι → Fin n → ℂ) (y x : Fin n → ℂ) (hx : ∀ j, herm H x (p j) = 0) :
    herm H x (proj H Γi p y) = 0 := by sorry
