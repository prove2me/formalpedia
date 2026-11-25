-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:50.566808+00:00
-- url     : https://prove2.me/theorems/f0a5fb25-a255-425e-a48f-bd0f7019e809
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison exists hess C bound adf0c8df653f: P2 M Ground Theory Heights  Heights Tube Form Comparison exists hess C bound adf0c8df653f
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison exists hess C bound adf0c8df653f construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison exists hess C bound adf0c8df653f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L81-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L81-L119

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f {N m : ℕ} (φ : Fin m → (Fin N → ℂ) → ℝ) (K : Set (Fin N → ℂ))
    (hK : IsCompact K) (U : Fin m → Set (Fin N → ℂ)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K ⊆ U i)
    (hφ : ∀ i, ContDiffOn ℝ 2 (φ i) (U i)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ x ∈ K, (hessC (φ i) x + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) x + (c : ℂ) • 1).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«exists_hessC_bound» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
