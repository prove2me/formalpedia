-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_fam_comp_6096efaf6c1c
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_fam_comp_6096efaf6c1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:11.376842+00:00
-- url     : https://prove2.me/theorems/e3a82f28-8c0d-4345-907c-34c8596e9eaf
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant fam comp 6096efaf6c1c: P2 M Ground Theory Heights  Heights Stokes Off Discriminant fam comp 6096efaf6c1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant fam comp 6096efaf6c1c construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant fam comp 6096efaf6c1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L162-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L162-L165

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_fam_comp_6096efaf6c1c {m : ℕ} {α β : Type*} (f : α → ℝ) (φ : Fin m → α → ℝ) (s : β → α) :
    (fun k => vecCons f φ k ∘ s) = (Fin.cons (f ∘ s) (fun k => φ k ∘ s) : Fin (m + 1) → β → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«fam_comp» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_fam_comp_6096efaf6c1c
