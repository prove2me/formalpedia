-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_of_sheet_fd294589a3b3
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_of_sheet_fd294589a3b3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:10.360358+00:00
-- url     : https://prove2.me/theorems/baf4e98e-068a-430e-b0db-fbd9654421c9
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant window of sheet fd294589a3b3: P2 M Ground Theory Heights  Heights Stokes Off Discriminant window of sheet fd294589a3b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant window of sheet fd294589a3b3 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant window of sheet fd294589a3b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L34-L46

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_of_sheet_fd294589a3b3 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    ∃ (V : Set (Fin D → ℂ)) (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ x ∈ W ∧
      DifferentiableOn ℂ s V ∧ (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«window_of_sheet» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_of_sheet_fd294589a3b3
