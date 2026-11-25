-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_proj_left
-- name    : PI.PolynomialProperness.CoreW.herm_proj_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:01.570901+00:00
-- url     : https://prove2.me/theorems/02cbd24b-199d-446d-977c-c12f5c0b9b3c
-- title:
--   Core W: herm proj left
-- statement:
--   The Core W construction uses the herm proj left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L124-L133

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

theorem PI.PolynomialProperness.CoreW.herm_proj_left (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (proj H Γi p y) (p j) = herm H y (p j) := by sorry
