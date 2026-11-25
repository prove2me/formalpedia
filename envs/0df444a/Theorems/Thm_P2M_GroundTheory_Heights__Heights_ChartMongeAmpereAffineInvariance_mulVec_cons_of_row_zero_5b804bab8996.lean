-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mulVec_cons_of_row_zero_5b804bab8996
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mulVec_cons_of_row_zero_5b804bab8996
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:33.073181+00:00
-- url     : https://prove2.me/theorems/086c765f-1c69-5879-9222-070fc547b45e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mul Vec cons of row zero 5b804bab8996: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mul Vec cons of
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mul Vec cons of row zero 5b804bab8996 construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mul Vec cons of row zero 5b804bab8996 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L17-L24

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mulVec_cons_of_row_zero_5b804bab8996 (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (y : Fin e → ℂ) :
    T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) =
      Fin.cons (T 0 0) ((fun i => T i.succ 0) + (T.submatrix Fin.succ Fin.succ) *ᵥ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«mulVec_cons_of_row_zero» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mulVec_cons_of_row_zero_5b804bab8996
