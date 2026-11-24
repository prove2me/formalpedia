-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:46.2938+00:00
-- url     : https://prove2.me/theorems/e70cb441-cc2b-495c-a25f-6e2c82f5a2e3
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet congr cfb570777011: P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet congr cfb570777011
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet congr cfb570777011 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant ma Dens sheet congr cfb570777011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L176-L182

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    (Ψ : Fin D → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ} {s s' : (Fin D → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (hs' : IsSheetAt J A x s') :
    ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s') (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s) (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«maDens_sheet_congr» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011
