-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_fracPairs_div_c2105d6455a7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_fracPairs_div_c2105d6455a7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:17.449376+00:00
-- url     : https://prove2.me/theorems/e2082859-3f3f-4a77-80b5-67670c0fe650
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor frac Pairs div c2105d6455a7: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor frac Pairs div c2105d6455a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor frac Pairs div c2105d6455a7 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor frac Pairs div c2105d6455a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L76-L88

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_fracPairs_div_c2105d6455a7 {c c' : (Σ k, ι k) → Φ} {p p' : Φ} (hp : (p, p) ∈ fracPairs c c')
    (hp' : (p', p') ∈ fracPairs c c') (h0 : p' ≠ 0) : (p / p', p / p') ∈ fracPairs c c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«fracPairs_div» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_fracPairs_div_c2105d6455a7
