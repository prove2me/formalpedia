-- Prove2me | Theorems.Thm_PI_LatIdxDetW_lidx_free
-- name    : PI.LatIdxDetW.lidx_free
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:12.706557+00:00
-- url     : https://prove2.me/theorems/016dda0f-6ba1-5d1f-8313-ff938d8870fe
-- title:
--   Lat Idx Det W: lidx free
-- statement:
--   The Lat Idx Det W construction uses the lidx free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L128-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L128-L152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

theorem PI.LatIdxDetW.lidx_free (w : HeightOneSpectrum R) {d : ℕ} (b : Basis (Fin d) K V) (γ : V ≃ₗ[K] V) :
    lidx w.asIdeal (Submodule.span R (Set.range b))
      ((Submodule.span R (Set.range b)).map ((γ.restrictScalars R : V ≃ₗ[R] V) : V →ₗ[R] V)) =
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton R⁰ (LinearMap.det (γ : V →ₗ[K] V))) := by sorry
