-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegFixedBallMass_chartDens_weight_mono_807676a64ee3
-- name    : P2M_GroundTheory_Heights__Heights_RegFixedBallMass_chartDens_weight_mono_807676a64ee3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:13.599269+00:00
-- url     : https://prove2.me/theorems/2575c741-880a-5a67-b660-8b8a69d98375
-- title:
--   P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass chart Dens weight mono 807676a64ee3: P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass chart Dens weight mono 807676a64ee3
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass chart Dens weight mono 807676a64ee3 construction uses the P2 M Ground Theory Heights  Heights Reg Fixed Ball Mass chart Dens weight mono 807676a64ee3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegFixedBallMass.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegFixedBallMass.lean#L23-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFixedBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOnChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CutOffNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegFixedBallMass
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
open GroundTheory.Heights₂.Heights.RegFixedBallMass
variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem P2M_GroundTheory_Heights__Heights_RegFixedBallMass_chartDens_weight_mono_807676a64ee3 (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {w w' : (Fin n → ℂ) → ℝ} (hw : ∀ x, w x ≤ w' x)
    (y : Fin (d + 1) → ℂ) :
    chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y ≤
      chartDens J A w' (vecCons (logReg u ε) fun _ => euclPot) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegFixedBallMass».«chartDens_weight_mono» := P2M_GroundTheory_Heights__Heights_RegFixedBallMass_chartDens_weight_mono_807676a64ee3
