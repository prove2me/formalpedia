-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_proj_bound
-- name    : PI.PolynomialProperness.CoreW.proj_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:17:26.353114+00:00
-- url     : https://prove2.me/theorems/ead0573e-7b5c-4bf4-b9f1-bebfa2a84e32
-- title:
--   Core W: proj bound
-- statement:
--   The Core W construction uses the proj bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L176-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L176-L181

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

theorem PI.PolynomialProperness.CoreW.proj_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) :
    eN (proj H Γi p y) ≤
      (Fintype.card ι : ℝ) * ((∑ j, ∑ k, ‖Γi j k‖) * (eN y * R)) * R := by sorry
