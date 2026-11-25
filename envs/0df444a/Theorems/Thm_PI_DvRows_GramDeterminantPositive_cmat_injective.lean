-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_cmat_injective
-- name    : PI.DvRows.GramDeterminantPositive.cmat_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:32:11.427893+00:00
-- url     : https://prove2.me/theorems/efc1b53d-f1aa-5b61-ba1e-5b4e021a4ac6
-- title:
--   Gram Determinant Positive: cmat injective
-- statement:
--   The Gram Determinant Positive construction uses the cmat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L314-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L314-L339

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

theorem PI.DvRows.GramDeterminantPositive.cmat_injective (A : HLat K) (σ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V)
    (hf : LinearIndependent K f) : Function.Injective (cmat A σ f).mulVec := by sorry
