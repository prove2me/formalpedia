-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffAt_comp_sheet_2341a309fa24
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffAt_comp_sheet_2341a309fa24
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:36.300977+00:00
-- url     : https://prove2.me/theorems/54b2cf3a-7921-42f0-a37b-a557242d85b7
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff At comp sheet 2341a309fa24: P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff At comp sheet 2341a309fa24
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff At comp sheet 2341a309fa24 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant cont Diff At comp sheet 2341a309fa24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L245-L250

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffAt_comp_sheet_2341a309fa24 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {g : (Fin n → ℂ) → ℝ} {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ}
    (hg : SmoothNear (zeroSet J) g) (hs : IsSheetAt J A x s) : ContDiffAt ℝ 2 (g ∘ s) (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«contDiffAt_comp_sheet» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_contDiffAt_comp_sheet_2341a309fa24
