-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_window_8615461adc16
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_window_8615461adc16
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:42.978799+00:00
-- url     : https://prove2.me/theorems/bbc7bc32-86fa-47e7-bfc5-7394585109da
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term window 8615461adc16: P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term window 8615461adc16
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term window 8615461adc16 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Term window 8615461adc16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L50-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L50-L83

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_window_8615461adc16 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ} {y : Fin D → ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} {W : Set (Fin n → ℂ)}
    (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s)
    (h1 : ∀ x s', A *ᵥ x = y → IsSheetAt J A x s' → IsSheetAt J A x s → H x s' = H x s)
    (h2 : ∀ x s', x ∈ zeroSet J → A *ᵥ x = y → x ∉ W → IsSheetAt J A x s' → H x s' = 0)
    (h3 : y ∈ V → s y ∉ W → H (s y) s = 0) (x : Fin n → ℂ) :
    sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«sheetTerm_window» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_window_8615461adc16
