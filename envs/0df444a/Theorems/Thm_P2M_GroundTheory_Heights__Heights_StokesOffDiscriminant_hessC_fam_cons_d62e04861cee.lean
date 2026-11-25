-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_hessC_fam_cons_d62e04861cee
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_hessC_fam_cons_d62e04861cee
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:59.97546+00:00
-- url     : https://prove2.me/theorems/4acff846-75d7-57cd-bd79-4467201fef1c
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant hess C fam cons d62e04861cee: P2 M Ground Theory Heights  Heights Stokes Off Discriminant hess C fam cons d62e04861cee
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant hess C fam cons d62e04861cee construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant hess C fam cons d62e04861cee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L128-L133

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_hessC_fam_cons_d62e04861cee {m : ℕ} (f : (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ)
    (z : Fin (m + 1) → ℂ) :
    (fun k => ReciprocityTheory.AnForm.hessC ((Fin.cons f φ : Fin (m + 1) → (Fin (m + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (ReciprocityTheory.AnForm.hessC f z) (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«hessC_fam_cons» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_hessC_fam_cons_d62e04861cee
