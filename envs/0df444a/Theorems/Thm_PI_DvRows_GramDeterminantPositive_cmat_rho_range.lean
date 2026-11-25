-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_cmat_rho_range
-- name    : PI.DvRows.GramDeterminantPositive.cmat_rho_range
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:46.288213+00:00
-- url     : https://prove2.me/theorems/8e73b17e-7e45-4c09-a6a4-583ec8fbed47
-- title:
--   Gram Determinant Positive: cmat rho range
-- statement:
--   The Gram Determinant Positive construction uses the cmat rho range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L365-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L365-L390

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

theorem PI.DvRows.GramDeterminantPositive.cmat_rho_range (A : HLat K) (e : Module.End K A.V) (he : e * e = e)
    (hCe : ∀ i j, IsCM (A.b.repr (e (A.b j)) i)) (σ : K →+* ℂ) {N m : ℕ} (w : Fin N → A.V)
    (hw : Submodule.span K (Set.range w) = LinearMap.range e) (y : Fin m → A.V)
    (hy : ∀ i, y i ∈ LinearMap.range e) :
    ∃ T0 : Matrix (Fin N) (Fin m) ℂ, cmat A (rho σ) y = cmat A σ w * T0 := by sorry
