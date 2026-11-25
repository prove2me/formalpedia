-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_finite_support_sheetTerm_window_0ddd9d1cf282
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_finite_support_sheetTerm_window_0ddd9d1cf282
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:28.679389+00:00
-- url     : https://prove2.me/theorems/46d9e3a5-b112-4e55-ab17-eeb42ecc0daf
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant finite support sheet Term window 0ddd9d1cf282: P2 M Ground Theory Heights  Heights Stokes Off Discriminant finite support sheet Term window
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant finite support sheet Term window 0ddd9d1cf282 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant finite support sheet Term window 0ddd9d1cf282 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L86-L95

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_finite_support_sheetTerm_window_0ddd9d1cf282 {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin D) (Fin n) ℂ} {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ}
    {y : Fin D → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (h : ∀ x, sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0) :
    (Function.support (sheetTerm J A H y)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«finite_support_sheetTerm_window» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_finite_support_sheetTerm_window_0ddd9d1cf282
