-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_continuousAt_sheet_0a0c684fe6fd
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_continuousAt_sheet_0a0c684fe6fd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:45.502842+00:00
-- url     : https://prove2.me/theorems/b560f71f-7af7-59bb-8b43-0673c75a5805
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant continuous At sheet 0a0c684fe6fd: P2 M Ground Theory Heights  Heights Stokes Off Discriminant continuous At sheet 0a0c684fe6fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant continuous At sheet 0a0c684fe6fd construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant continuous At sheet 0a0c684fe6fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L184-L188

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_continuousAt_sheet_0a0c684fe6fd {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    ContinuousAt s (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«continuousAt_sheet» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_continuousAt_sheet_0a0c684fe6fd
