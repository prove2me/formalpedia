-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
-- name    : P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:18.739265+00:00
-- url     : https://prove2.me/theorems/2011fd86-4ca0-41ec-a6e9-d107748d66e7
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Sum Measurable sheet eventually Eq f5b44630f2f2: P2 M Ground Theory Heights  Heights Sheet Sum Measurable sheet eventually Eq f5b44630f2f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Sum Measurable sheet eventually Eq f5b44630f2f2 construction uses the P2 M Ground Theory Heights  Heights Sheet Sum Measurable sheet eventually Eq f5b44630f2f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L39-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
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
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (hs' : IsSheetAt J A x s') : s' =ᶠ[𝓝 (A *ᵥ x)] s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetSumMeasurable».«sheet_eventuallyEq» := P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
