-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_abs_maDens_cons_le_50c543526b9e
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_abs_maDens_cons_le_50c543526b9e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:23.284408+00:00
-- url     : https://prove2.me/theorems/0fa3b5bc-8628-5c77-a0f2-c2f3c566a131
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison abs ma Dens cons le 50c543526b9e: P2 M Ground Theory Heights  Heights Tube Form Comparison abs ma Dens cons le 50c543526b9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison abs ma Dens cons le 50c543526b9e construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison abs ma Dens cons le 50c543526b9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L171-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L171-L246

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_abs_maDens_cons_le_50c543526b9e {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y)
    (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (s y)) {c : ℝ}
    (hb : ∀ i, (hessC (φ i) (s y) + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) (s y) + (c : ℂ) • 1).PosSemidef)
    (hM : (hessC (g ∘ s) y).PosSemidef) :
    |maDens (fun k => vecCons g φ k ∘ s) y| ≤
      3 ^ (d + 1) * c ^ d * maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«abs_maDens_cons_le» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_abs_maDens_cons_le_50c543526b9e
