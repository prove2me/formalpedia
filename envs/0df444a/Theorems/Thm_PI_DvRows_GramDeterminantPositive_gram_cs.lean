-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_gram_cs
-- name    : PI.DvRows.GramDeterminantPositive.gram_cs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:28.026451+00:00
-- url     : https://prove2.me/theorems/c7d5aa86-ece4-4952-bb67-8213891124dc
-- title:
--   Gram Determinant Positive: gram cs
-- statement:
--   The Gram Determinant Positive construction uses the gram cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L63-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L63-L127

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
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem PI.DvRows.GramDeterminantPositive.gram_cs {k : Type*} [Fintype k] [DecidableEq k] (P Q : Matrix m k ℂ) :
    ‖(Pᴴ * Q).det‖ ^ 2 ≤ (Pᴴ * P).det.re * (Qᴴ * Q).det.re := by sorry
