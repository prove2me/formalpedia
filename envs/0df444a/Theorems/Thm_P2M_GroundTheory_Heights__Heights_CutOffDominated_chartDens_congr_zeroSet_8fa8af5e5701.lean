-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
-- name    : P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:05.598829+00:00
-- url     : https://prove2.me/theorems/286181e7-7008-474d-bd39-09c01cf2119c
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Dominated chart Dens congr zero Set 8fa8af5e5701: P2 M Ground Theory Heights  Heights Cut Off Dominated chart Dens congr zero Set 8fa8af5e5701
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Dominated chart Dens congr zero Set 8fa8af5e5701 construction uses the P2 M Ground Theory Heights  Heights Cut Off Dominated chart Dens congr zero Set 8fa8af5e5701 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffDominated.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffDominated.lean#L18-L24

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

theorem P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f g : (Fin n → ℂ) → ℝ} (h : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    chartDens J A f φ = chartDens J A g φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffDominated».«chartDens_congr_zeroSet» := P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
