-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
-- name    : P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:27.473943+00:00
-- url     : https://prove2.me/theorems/86edd9dc-7a15-467d-a160-b0ae2e19d1c3
-- title:
--   P2 M Ground Theory Heights  Heights smooth Near of cont Diff 8ca53b5543f3: P2 M Ground Theory Heights  Heights smooth Near of cont Diff 8ca53b5543f3
-- statement:
--   The P2 M Ground Theory Heights  Heights smooth Near of cont Diff 8ca53b5543f3 construction uses the P2 M Ground Theory Heights  Heights smooth Near of cont Diff 8ca53b5543f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L244-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L244-L246

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3 {n : ℕ} {S : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ}
    (h : ContDiff ℝ ∞ φ) : SmoothNear S φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«smoothNear_of_contDiff» := P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
