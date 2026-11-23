-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_pd_det_real
-- name    : PI.DvRows.GramDeterminantPositive.pd_det_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:44.860972+00:00
-- url     : https://prove2.me/theorems/872982bb-e72b-4004-8e96-afc6a508f933
-- title:
--   Gram Determinant Positive: pd det real
-- statement:
--   The Gram Determinant Positive construction uses the pd det real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L23-L27

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
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem PI.DvRows.GramDeterminantPositive.pd_det_real {A : Matrix n n ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 < A.det.re := by sorry
