-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_prod_wblk_dd968f239759
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_prod_wblk_dd968f239759
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:25.821318+00:00
-- url     : https://prove2.me/theorems/8d4b7d3c-03d6-4f86-b289-d48fc78f12a3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor prod wblk dd968f239759: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor prod wblk dd968f239759
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor prod wblk dd968f239759 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor prod wblk dd968f239759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L128-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_prod_wblk_dd968f239759 {M : Type} [CommMonoid M] (g : T.WBlk → M) :
    ∏ k, g k = g .base * g .det * g .line0 * g .line1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«prod_wblk» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_prod_wblk_dd968f239759
