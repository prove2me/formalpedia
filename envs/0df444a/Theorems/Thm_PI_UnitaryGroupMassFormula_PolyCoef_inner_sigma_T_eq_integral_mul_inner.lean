-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_inner_sigma_T_eq_integral_mul_inner
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.inner_sigma_T_eq_integral_mul_inner
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:22.561066+00:00
-- url     : https://prove2.me/theorems/64258fd2-596a-4e9e-b049-370947bfab6a
-- title:
--   Poly Coef: inner sigma T eq integral mul inner
-- statement:
--   The Poly Coef construction uses the inner sigma T eq integral mul inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L45-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}

theorem PI.UnitaryGroupMassFormula.PolyCoef.inner_sigma_T_eq_integral_mul_inner [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    (f : C(UG N, ℂ)) (u : S) (w : H) (h : UG N) :
    ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ =
      ∫ x, f x * ⟪w, σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) u⟫_ℂ ∂(muU N) := by sorry
