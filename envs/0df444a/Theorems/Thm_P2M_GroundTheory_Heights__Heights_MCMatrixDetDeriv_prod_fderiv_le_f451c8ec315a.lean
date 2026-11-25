-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCMatrixDetDeriv_prod_fderiv_le_f451c8ec315a
-- name    : P2M_GroundTheory_Heights__Heights_MCMatrixDetDeriv_prod_fderiv_le_f451c8ec315a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:05.809431+00:00
-- url     : https://prove2.me/theorems/b5035ebe-10cf-518e-998f-64c9aff70197
-- title:
--   P2 M Ground Theory Heights  Heights MCMatrix Det Deriv prod fderiv le f451c8ec315a: P2 M Ground Theory Heights  Heights MCMatrix Det Deriv prod fderiv le f451c8ec315a
-- statement:
--   The P2 M Ground Theory Heights  Heights MCMatrix Det Deriv prod fderiv le f451c8ec315a construction uses the P2 M Ground Theory Heights  Heights MCMatrix Det Deriv prod fderiv le f451c8ec315a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PMatrixDetDeriv.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PMatrixDetDeriv.lean#L12-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PMatrixDetDeriv
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
open Matrix
open GroundTheory.Heights₂.Heights.MCMatrixDetDeriv

theorem P2M_GroundTheory_Heights__Heights_MCMatrixDetDeriv_prod_fderiv_le_f451c8ec315a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (g : ι → E → ℂ) (p : E) (A B : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (g i) p ∧ ‖g i p‖ ≤ A ∧ ‖fderiv ℝ (g i) p‖ ≤ B) :
    DifferentiableAt ℝ (fun q => ∏ i ∈ s, g i q) p ∧
      ‖fderiv ℝ (fun q => ∏ i ∈ s, g i q) p‖ ≤ (s.card : ℝ) * A ^ (s.card - 1) * B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCMatrixDetDeriv».«prod_fderiv_le» := P2M_GroundTheory_Heights__Heights_MCMatrixDetDeriv_prod_fderiv_le_f451c8ec315a
