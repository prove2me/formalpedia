-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_gramPl_eq
-- name    : PI.DvRows.GramDeterminantPositive.gramPl_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:51.305163+00:00
-- url     : https://prove2.me/theorems/bd401a8c-615b-4f91-a785-a496fb928d7c
-- title:
--   Gram Determinant Positive: gram Pl eq
-- statement:
--   The Gram Determinant Positive construction uses the gram Pl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L191-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L191-L199

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

theorem PI.DvRows.GramDeterminantPositive.gramPl_eq (A : HLat K) (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    Formalism.HN.gramPl A.b A.X v f =
      ((A.X v)⁻¹ * cmat A v.embedding f)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding f) := by sorry
