-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_hmatrix_eq
-- name    : PI.DvRows.GramDeterminantPositive.hmatrix_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:10.952891+00:00
-- url     : https://prove2.me/theorems/fdb61d25-551c-5d63-b7b3-043a6203379b
-- title:
--   Gram Determinant Positive: hmatrix eq
-- statement:
--   The Gram Determinant Positive construction uses the hmatrix eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L216-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L216-L223

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

theorem PI.DvRows.GramDeterminantPositive.hmatrix_eq (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) {m m' : ℕ}
    (f : Fin m → A.V) (g : Fin m' → A.V) :
    (Matrix.of fun i j => φ (h (f i) (g j))) = (cmat A (rho φ) f)ᴴ * hmat A h φ * cmat A φ g := by sorry
