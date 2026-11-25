-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_chartMass_conj_47d12006171a
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_chartMass_conj_47d12006171a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:41.329484+00:00
-- url     : https://prove2.me/theorems/08d528af-0507-4fdb-8ffb-dc4bb086db2c
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance chart Mass conj 47d12006171a: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance chart Mass conj 47d12006
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance chart Mass conj 47d12006171a construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance chart Mass conj 47d12006171a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L63-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_chartMass_conj_47d12006171a (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (hdet : T.det ≠ 0) :
    chartMass (Tᴴ * M * T) = chartMass M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«chartMass_conj» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_chartMass_conj_47d12006171a
