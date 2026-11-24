-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffOn_comp_section_a91a7dee72e2
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffOn_comp_section_a91a7dee72e2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:07.171972+00:00
-- url     : https://prove2.me/theorems/ed17ec8f-6b0d-4a51-8252-b1cb2dfd36c5
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff On comp section a91a7dee72e2: P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff On comp section a91a7dee72e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff On comp section a91a7dee72e2 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff On comp section a91a7dee72e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L195-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L195-L201

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffOn_comp_section_a91a7dee72e2 {J : Ideal (MvPolynomial (Fin n) ℂ)} {g : (Fin n → ℂ) → ℝ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} (hg : SmoothNear (zeroSet J) g)
    (hV : IsOpen V) (hsd : DifferentiableOn ℂ s V) (hsZ : ∀ y ∈ V, s y ∈ zeroSet J) :
    ContDiffOn ℝ ∞ (g ∘ s) V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«contDiffOn_comp_section» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffOn_comp_section_a91a7dee72e2
