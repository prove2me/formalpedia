-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_sigma_hmatrix
-- name    : PI.DvRows.GramDeterminantPositive.sigma_hmatrix
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:11.040068+00:00
-- url     : https://prove2.me/theorems/476f62da-df70-40b0-80dd-4cb20c7922d0
-- title:
--   Gram Determinant Positive: sigma hmatrix
-- statement:
--   The Gram Determinant Positive construction uses the sigma hmatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L241-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L241-L245

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
variable (hC1 : ∀ i j, IsCM (h (A.b i) (A.b j)))
  (hC3 : ∀ (v : InfinitePlace K) i j,
    Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j)))
include hC3

theorem PI.DvRows.GramDeterminantPositive.sigma_hmatrix (v : InfinitePlace K) {m m' : ℕ} (f : Fin m → A.V) (g : Fin m' → A.V) :
    (Matrix.of fun i j => v.embedding (h (f i) (g j))) =
      ((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding g) := by sorry
