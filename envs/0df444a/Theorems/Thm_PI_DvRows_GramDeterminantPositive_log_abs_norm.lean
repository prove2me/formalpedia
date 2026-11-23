-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_log_abs_norm
-- name    : PI.DvRows.GramDeterminantPositive.log_abs_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:04.811778+00:00
-- url     : https://prove2.me/theorems/90f2249a-b721-4eba-8db7-b6eb5f8b5313
-- title:
--   Gram Determinant Positive: log abs norm
-- statement:
--   The Gram Determinant Positive construction uses the log abs norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L355-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L355-L363

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

theorem PI.DvRows.GramDeterminantPositive.log_abs_norm [IsTotallyComplex K] (x : K) (hx : x ≠ 0) :
    Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log ‖v.embedding x‖ := by sorry
