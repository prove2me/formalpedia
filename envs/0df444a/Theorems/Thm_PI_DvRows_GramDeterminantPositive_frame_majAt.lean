-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_frame_majAt
-- name    : PI.DvRows.GramDeterminantPositive.frame_majAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:28.709948+00:00
-- url     : https://prove2.me/theorems/7e4b3076-6a89-4ab6-b7bb-a35a44544688
-- title:
--   Gram Determinant Positive: frame maj At
-- statement:
--   The Gram Determinant Positive construction uses the frame maj At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L201-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L201-L206

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

theorem PI.DvRows.GramDeterminantPositive.frame_majAt (A : HLat K) (v : InfinitePlace K) :
    ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ =
      Matrix.of fun k l => Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b k) (A.b l) := by sorry
