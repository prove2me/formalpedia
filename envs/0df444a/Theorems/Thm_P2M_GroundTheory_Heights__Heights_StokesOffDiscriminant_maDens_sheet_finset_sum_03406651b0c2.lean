-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_finset_sum_03406651b0c2
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_finset_sum_03406651b0c2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:17.69048+00:00
-- url     : https://prove2.me/theorems/90a8c853-f883-4946-8a1c-3c876990fb7e
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet finset sum 03406651b0c2: P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet finset sum 03406651b0c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet finset sum 03406651b0c2 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet finset sum 03406651b0c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L252-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L252-L270

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
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
open GroundTheory.Heights₂.Heights.StokesOffDiscriminant
variable {n D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_finset_sum_03406651b0c2 {ι : Type*} (t : Finset ι) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (D + 1)) (Fin n) ℂ} (F : (Fin n → ℂ) → ℝ) (f : ι → (Fin n → ℂ) → ℝ)
    (φ : Fin D → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ} {s : (Fin (D + 1) → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (hsum : ∀ z ∈ zeroSet J, F z = ∑ i ∈ t, f i z)
    (hf : ∀ i ∈ t, SmoothNear (zeroSet J) (f i)) :
    ReciprocityTheory.AnForm.maDens (fun k => vecCons F φ k ∘ s) (A *ᵥ x) =
      ∑ i ∈ t, ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s) (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«maDens_sheet_finset_sum» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_finset_sum_03406651b0c2
