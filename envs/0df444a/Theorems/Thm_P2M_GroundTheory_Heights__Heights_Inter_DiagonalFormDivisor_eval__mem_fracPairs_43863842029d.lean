-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_eval__mem_fracPairs_43863842029d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_eval__mem_fracPairs_43863842029d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:17.991775+00:00
-- url     : https://prove2.me/theorems/8b9f67fe-cd17-5f81-8a36-58d4d4166e52
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor eval  mem frac Pairs 43863842029d: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor eval  mem frac Pairs 43863842029d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor eval  mem frac Pairs 43863842029d construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor eval  mem frac Pairs 43863842029d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L90-L96

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_eval__mem_fracPairs_43863842029d {R : Type} [CommRing R] (f : R →+* Φ) {c c' : (Σ k, ι k) → Φ}
    (hf : ∀ y, (f y, f y) ∈ fracPairs c c') {n : Type} (z z' : n → Φ) (hz : ∀ j, (z j, z' j) ∈ fracPairs c c')
    (G : MvPolynomial n R) : (eval₂ f z G, eval₂ f z' G) ∈ fracPairs c c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«eval₂_mem_fracPairs» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_eval__mem_fracPairs_43863842029d
