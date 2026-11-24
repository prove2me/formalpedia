-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_of_det_ne_zero_08ac665d1d09
-- name    : P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_of_det_ne_zero_08ac665d1d09
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:23.480099+00:00
-- url     : https://prove2.me/theorems/327d361e-c286-4c30-9894-3cfed49795c3
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Only Null exists sheet of det ne zero 08ac665d1d09: P2 M Ground Theory Heights  Heights Sheet Only Null exists sheet of det ne zero 08ac665d1d09
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Only Null exists sheet of det ne zero 08ac665d1d09 construction uses the P2 M Ground Theory Heights  Heights Sheet Only Null exists sheet of det ne zero 08ac665d1d09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L73-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L73-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
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
noncomputable section
open GroundTheory.Heights₂.Heights.SheetOnlyNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_of_det_ne_zero_08ac665d1d09 {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J A' x s' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetOnlyNull».«exists_sheet_of_det_ne_zero» := P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_of_det_ne_zero_08ac665d1d09
