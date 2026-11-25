-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_add_84a6f63f8f9d
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_add_84a6f63f8f9d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:09.540334+00:00
-- url     : https://prove2.me/theorems/1ce2601b-ffb1-4354-93a4-834ecdf09d57
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons add 84a6f63f8f9d: P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons add 84a6f63f8f9d
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons add 84a6f63f8f9d construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons add 84a6f63f8f9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L135-L144

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_add_84a6f63f8f9d {m : ℕ} (f g : (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ)
    (z : Fin (m + 1) → ℂ) (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    ReciprocityTheory.AnForm.maDens (Fin.cons (fun w => f w + g w) φ) z =
      ReciprocityTheory.AnForm.maDens (Fin.cons f φ) z + ReciprocityTheory.AnForm.maDens (Fin.cons g φ) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«maDens_cons_add» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_add_84a6f63f8f9d
