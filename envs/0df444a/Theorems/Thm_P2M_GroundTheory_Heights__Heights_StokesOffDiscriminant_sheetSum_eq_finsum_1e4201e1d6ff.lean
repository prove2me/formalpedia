-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_eq_finsum_1e4201e1d6ff
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_eq_finsum_1e4201e1d6ff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:58.594392+00:00
-- url     : https://prove2.me/theorems/229e17db-fb0b-48fb-af56-e816b301443a
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Sum eq finsum 1e4201e1d6ff: P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Sum eq finsum 1e4201e1d6ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Sum eq finsum 1e4201e1d6ff construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant sheet Sum eq finsum 1e4201e1d6ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L28-L32

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

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_eq_finsum_1e4201e1d6ff (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin D) (Fin n) ℂ)
    (H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ) (y : Fin D → ℂ) :
    sheetSum J A H y = ∑ᶠ x, sheetTerm J A H y x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«sheetSum_eq_finsum» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_eq_finsum_1e4201e1d6ff
