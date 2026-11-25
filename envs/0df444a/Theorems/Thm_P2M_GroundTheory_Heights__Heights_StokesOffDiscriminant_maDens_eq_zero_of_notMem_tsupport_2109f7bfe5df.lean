-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_eq_zero_of_notMem_tsupport_2109f7bfe5df
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_eq_zero_of_notMem_tsupport_2109f7bfe5df
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:23.993803+00:00
-- url     : https://prove2.me/theorems/dbcc2eea-9411-4477-b671-d30519cdf467
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens eq zero of not Mem tsupport 2109f7bfe5df: P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens eq zero of not Mem tsu
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens eq zero of not Mem tsupport 2109f7bfe5df construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens eq zero of not Mem tsupport 2109f7bfe5df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L167-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L167-L174

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_eq_zero_of_notMem_tsupport_2109f7bfe5df {m : ℕ} (f : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) {s : (Fin (m + 1) → ℂ) → Fin n → ℂ} {y : Fin (m + 1) → ℂ}
    (hs : ContinuousAt s y) (hy : s y ∉ tsupport f) :
    ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s) y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«maDens_eq_zero_of_notMem_tsupport» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_eq_zero_of_notMem_tsupport_2109f7bfe5df
