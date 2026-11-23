-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_map_det_of
-- name    : PI.DvRows.GramDeterminantPositive.map_det_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:30.732126+00:00
-- url     : https://prove2.me/theorems/47a63610-bbda-46d4-8d88-379ad5e057c5
-- title:
--   Gram Determinant Positive: map det of
-- statement:
--   The Gram Determinant Positive construction uses the map det of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L225-L227

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

theorem PI.DvRows.GramDeterminantPositive.map_det_of (φ : K →+* ℂ) {d : ℕ} (F : Fin d → Fin d → K) :
    φ (Matrix.of F).det = (Matrix.of fun i j => φ (F i j)).det := by sorry
