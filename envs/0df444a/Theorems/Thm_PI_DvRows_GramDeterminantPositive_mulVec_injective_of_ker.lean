-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_mulVec_injective_of_ker
-- name    : PI.DvRows.GramDeterminantPositive.mulVec_injective_of_ker
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:09.935472+00:00
-- url     : https://prove2.me/theorems/50d8d3c0-7cc9-5cb5-b2f5-de27e68b7f14
-- title:
--   Gram Determinant Positive: mul Vec injective of ker
-- statement:
--   The Gram Determinant Positive construction uses the mul Vec injective of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L57-L59

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

theorem PI.DvRows.GramDeterminantPositive.mulVec_injective_of_ker {m k : Type*} [Fintype k] {P : Matrix m k ℂ}
    (h : ∀ v, P *ᵥ v = 0 → v = 0) : Function.Injective P.mulVec := by sorry
