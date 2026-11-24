-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_weight_window_dd35cc3747df
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_weight_window_dd35cc3747df
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:35:01.155131+00:00
-- url     : https://prove2.me/theorems/a3fb8f60-880a-4f3b-ac84-9e29d1f39c2b
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term weight window dd35cc3747df: P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term weight window dd35cc3747df
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term weight window dd35cc3747df construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term weight window dd35cc3747df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L205-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L205-L220

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_weight_window_dd35cc3747df {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} {W : Set (Fin n → ℂ)}
    (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f : (Fin n → ℂ) → ℝ)
    (hfW : tsupport f ⊆ W) (Ψ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin D → ℂ) (x : Fin n → ℂ) :
    sheetTerm J A (fun x s' => f x * ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s') y) y x =
      if y ∈ V ∧ x = s y then f (s y) * ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s) y else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«sheetTerm_weight_window» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_weight_window_dd35cc3747df
