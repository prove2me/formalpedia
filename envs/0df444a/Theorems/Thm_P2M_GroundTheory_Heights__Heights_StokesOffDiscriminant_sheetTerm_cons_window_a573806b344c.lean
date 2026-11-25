-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_cons_window_a573806b344c
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_cons_window_a573806b344c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:46.020911+00:00
-- url     : https://prove2.me/theorems/f20c7ef7-cb02-42da-a149-ef7397ad2b48
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term cons window a573806b344c: P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term cons window a573806b344c
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term cons window a573806b344c construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term cons window a573806b344c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L224-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L224-L243

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_cons_window_a573806b344c {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (D + 1)) (Fin n) ℂ} {s : (Fin (D + 1) → ℂ) → Fin n → ℂ}
    {V : Set (Fin (D + 1) → ℂ)} {W : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hsd : DifferentiableOn ℂ s V) (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f G : (Fin n → ℂ) → ℝ)
    (hfW : tsupport f ⊆ W) (φ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (x : Fin n → ℂ) :
    sheetTerm J A (fun x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s') y) y x =
      if y ∈ V ∧ x = s y then G (s y) * ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s) y
      else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«sheetTerm_cons_window» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_cons_window_a573806b344c
