-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_nonneg_7dddc6a166b7
-- name    : P2M_GroundTheory_Heights__Heights_gramVol_nonneg_7dddc6a166b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:46.551135+00:00
-- url     : https://prove2.me/theorems/cc0e2046-3450-44b3-b620-c8322b898858
-- title:
--   P2 M Ground Theory Heights  Heights gram Vol nonneg 7dddc6a166b7: P2 M Ground Theory Heights  Heights gram Vol nonneg 7dddc6a166b7
-- statement:
--   The P2 M Ground Theory Heights  Heights gram Vol nonneg 7dddc6a166b7 construction uses the P2 M Ground Theory Heights  Heights gram Vol nonneg 7dddc6a166b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L16-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_gramVol_nonneg_7dddc6a166b7 {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gramVol_nonneg» := P2M_GroundTheory_Heights__Heights_gramVol_nonneg_7dddc6a166b7
