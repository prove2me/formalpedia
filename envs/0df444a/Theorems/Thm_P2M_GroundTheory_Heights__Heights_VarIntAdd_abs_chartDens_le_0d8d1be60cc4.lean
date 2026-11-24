-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_abs_chartDens_le_0d8d1be60cc4
-- name    : P2M_GroundTheory_Heights__Heights_VarIntAdd_abs_chartDens_le_0d8d1be60cc4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:59.506837+00:00
-- url     : https://prove2.me/theorems/d29b9e5b-98bd-4825-8e95-fea7fcdb9197
-- title:
--   P2 M Ground Theory Heights  Heights Var Int Add abs chart Dens le 0d8d1be60cc4: P2 M Ground Theory Heights  Heights Var Int Add abs chart Dens le 0d8d1be60cc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Int Add abs chart Dens le 0d8d1be60cc4 construction uses the P2 M Ground Theory Heights  Heights Var Int Add abs chart Dens le 0d8d1be60cc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L56-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.VarIntAdd

theorem P2M_GroundTheory_Heights__Heights_VarIntAdd_abs_chartDens_le_0d8d1be60cc4 {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (w : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ)
    (y : Fin k → ℂ) : |chartDens J A w φ y| ≤ chartAbsDens J A w φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarIntAdd».«abs_chartDens_le» := P2M_GroundTheory_Heights__Heights_VarIntAdd_abs_chartDens_le_0d8d1be60cc4
