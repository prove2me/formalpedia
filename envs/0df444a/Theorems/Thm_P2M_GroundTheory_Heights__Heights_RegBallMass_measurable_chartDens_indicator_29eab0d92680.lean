-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegBallMass_measurable_chartDens_indicator_29eab0d92680
-- name    : P2M_GroundTheory_Heights__Heights_RegBallMass_measurable_chartDens_indicator_29eab0d92680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:22.082774+00:00
-- url     : https://prove2.me/theorems/ea7bbc95-1e8f-4164-b323-e972eb8fe26b
-- title:
--   P2 M Ground Theory Heights  Heights Reg Ball Mass measurable chart Dens indicator 29eab0d92680: P2 M Ground Theory Heights  Heights Reg Ball Mass measurable chart Dens indicator 29eab0d92680
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Ball Mass measurable chart Dens indicator 29eab0d92680 construction uses the P2 M Ground Theory Heights  Heights Reg Ball Mass measurable chart Dens indicator 29eab0d92680 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegBallMass.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegBallMass.lean#L48-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFixedBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegBallMass
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
open GroundTheory.Heights₂.Heights.RegBallMass
variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem P2M_GroundTheory_Heights__Heights_RegBallMass_measurable_chartDens_indicator_29eab0d92680 (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) :
    Measurable (chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegBallMass».«measurable_chartDens_indicator» := P2M_GroundTheory_Heights__Heights_RegBallMass_measurable_chartDens_indicator_29eab0d92680
