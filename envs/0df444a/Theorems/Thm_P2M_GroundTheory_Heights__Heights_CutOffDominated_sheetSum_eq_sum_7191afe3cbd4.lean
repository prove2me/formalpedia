-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_sheetSum_eq_sum_7191afe3cbd4
-- name    : P2M_GroundTheory_Heights__Heights_CutOffDominated_sheetSum_eq_sum_7191afe3cbd4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:11.660621+00:00
-- url     : https://prove2.me/theorems/1e254c2e-3fe5-4a34-90d4-77df1996fee7
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Dominated sheet Sum eq sum 7191afe3cbd4: P2 M Ground Theory Heights  Heights Cut Off Dominated sheet Sum eq sum 7191afe3cbd4
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Dominated sheet Sum eq sum 7191afe3cbd4 construction uses the P2 M Ground Theory Heights  Heights Cut Off Dominated sheet Sum eq sum 7191afe3cbd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffDominated.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffDominated.lean#L28-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
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
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffDominated
variable {n d : ℕ}
open Classical

theorem P2M_GroundTheory_Heights__Heights_CutOffDominated_sheetSum_eq_sum_7191afe3cbd4 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffDominated».«sheetSum_eq_sum» := P2M_GroundTheory_Heights__Heights_CutOffDominated_sheetSum_eq_sum_7191afe3cbd4
