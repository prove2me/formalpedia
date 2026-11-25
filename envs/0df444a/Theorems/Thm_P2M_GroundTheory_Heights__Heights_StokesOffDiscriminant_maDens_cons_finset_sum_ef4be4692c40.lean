-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_finset_sum_ef4be4692c40
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_finset_sum_ef4be4692c40
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:47.024553+00:00
-- url     : https://prove2.me/theorems/af763fce-8037-58de-aeba-3f4e32a8ac0f
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons finset sum ef4be4692c40: P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons finset sum ef4be4692c40
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons finset sum ef4be4692c40 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens cons finset sum ef4be4692c40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L146-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L146-L160

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_finset_sum_ef4be4692c40 {m : ℕ} {ι : Type*} (t : Finset ι)
    (g : ι → (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ) (z : Fin (m + 1) → ℂ)
    (hg : ∀ i ∈ t, ContDiffAt ℝ 2 (g i) z) :
    ReciprocityTheory.AnForm.maDens (Fin.cons (fun w => ∑ i ∈ t, g i w) φ) z =
      ∑ i ∈ t, ReciprocityTheory.AnForm.maDens (Fin.cons (g i) φ) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«maDens_cons_finset_sum» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_finset_sum_ef4be4692c40
