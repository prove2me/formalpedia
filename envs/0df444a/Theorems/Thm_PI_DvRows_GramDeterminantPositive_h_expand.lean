-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_h_expand
-- name    : PI.DvRows.GramDeterminantPositive.h_expand
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:21.224971+00:00
-- url     : https://prove2.me/theorems/509e3d7a-8f6f-47c6-9a88-c7ab58eb40ff
-- title:
--   Gram Determinant Positive: h expand
-- statement:
--   The Gram Determinant Positive construction uses the h expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L208-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L208-L214

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

theorem PI.DvRows.GramDeterminantPositive.h_expand (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (x y : A.V) :
    h x y = ∑ k, ∑ l, star (A.b.repr x k) * A.b.repr y l * h (A.b k) (A.b l) := by sorry
