-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:33.043465+00:00
-- url     : https://prove2.me/theorems/083bb144-aa0c-4c0a-abee-db75a0f6fa16
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance herm Chart Pot conj 179aa3d33806: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance herm Chart Pot conj
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance herm Chart Pot conj 179aa3d33806 construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance herm Chart Pot conj 179aa3d33806 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L31-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L31-L61

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806 (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (ht : T 0 0 ≠ 0) (y : Fin e → ℂ) :
    hermChartPot (Tᴴ * M * T) y =
      hermChartPot M ((T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) +
        Real.log ‖T 0 0‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«hermChartPot_conj» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806
