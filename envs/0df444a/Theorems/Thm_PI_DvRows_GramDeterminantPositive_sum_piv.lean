-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_sum_piv
-- name    : PI.DvRows.GramDeterminantPositive.sum_piv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:41.859658+00:00
-- url     : https://prove2.me/theorems/bbf322ad-c1db-4db7-82b7-a7df0af802a7
-- title:
--   Gram Determinant Positive: sum piv
-- statement:
--   The Gram Determinant Positive construction uses the sum piv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L311-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L311-L312

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

theorem PI.DvRows.GramDeterminantPositive.sum_piv (F : InfinitePlace K → ℝ) : ∑ v, F (piv v) = ∑ v, F v := by sorry
