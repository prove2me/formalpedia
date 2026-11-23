-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_psd_det_real
-- name    : PI.DvRows.GramDeterminantPositive.psd_det_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:38.772309+00:00
-- url     : https://prove2.me/theorems/9babe831-057b-4d56-a2d6-24508a661a0b
-- title:
--   Gram Determinant Positive: psd det real
-- statement:
--   The Gram Determinant Positive construction uses the psd det real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L17-L21

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

theorem PI.DvRows.GramDeterminantPositive.psd_det_real {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 ≤ A.det.re := by sorry
