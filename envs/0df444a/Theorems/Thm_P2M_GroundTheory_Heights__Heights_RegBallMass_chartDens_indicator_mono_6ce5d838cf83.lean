-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegBallMass_chartDens_indicator_mono_6ce5d838cf83
-- name    : P2M_GroundTheory_Heights__Heights_RegBallMass_chartDens_indicator_mono_6ce5d838cf83
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:17.569906+00:00
-- url     : https://prove2.me/theorems/0c3d10bd-7320-4983-834d-89d2a022729f
-- title:
--   P2 M Ground Theory Heights  Heights Reg Ball Mass chart Dens indicator mono 6ce5d838cf83: P2 M Ground Theory Heights  Heights Reg Ball Mass chart Dens indicator mono 6ce5d838cf83
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Ball Mass chart Dens indicator mono 6ce5d838cf83 construction uses the P2 M Ground Theory Heights  Heights Reg Ball Mass chart Dens indicator mono 6ce5d838cf83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegBallMass.lean#L21-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegBallMass.lean#L21-L46

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

theorem P2M_GroundTheory_Heights__Heights_RegBallMass_chartDens_indicator_mono_6ce5d838cf83 (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegBallMass».«chartDens_indicator_mono» := P2M_GroundTheory_Heights__Heights_RegBallMass_chartDens_indicator_mono_6ce5d838cf83
