-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_stokes_9e29c9457aa1
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_stokes_9e29c9457aa1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:17.950627+00:00
-- url     : https://prove2.me/theorems/29e3e83b-3252-44bd-9e69-d008e0c69251
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant window stokes 9e29c9457aa1: P2 M Ground Theory Heights  Heights Stokes Off Discriminant window stokes 9e29c9457aa1
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant window stokes 9e29c9457aa1 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant window stokes 9e29c9457aa1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L272-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L272-L331

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_stokes_9e29c9457aa1 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (D + 1)) (Fin n) ℂ}
    {s : (Fin (D + 1) → ℂ) → Fin n → ℂ} {V : Set (Fin (D + 1) → ℂ)} {W : Set (Fin n → ℂ)}
    (hV : IsOpen V) (hsd : DifferentiableOn ℂ s V) (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f G : (Fin n → ℂ) → ℝ)
    (φ : Fin D → (Fin n → ℂ) → ℝ) (hf : SmoothNear (zeroSet J) f) (hG : SmoothNear (zeroSet J) G)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) (hfc : HasCompactSupport f) (hfW : tsupport f ⊆ W) :
    chartInt J A f (vecCons G φ) = chartInt J A G (vecCons f φ) ∧
      Integrable (chartDens J A f (vecCons G φ)) ∧ Integrable (chartDens J A G (vecCons f φ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«window_stokes» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_stokes_9e29c9457aa1
