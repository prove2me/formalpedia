-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_mem_fracPairs_of_9d1a77e172f2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_mem_fracPairs_of_9d1a77e172f2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:01.951402+00:00
-- url     : https://prove2.me/theorems/acd97948-27cd-4443-acfd-fe3d69d21de1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor mem frac Pairs of 9d1a77e172f2: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor mem frac Pairs of 9d1a77e172f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor mem frac Pairs of 9d1a77e172f2 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor mem frac Pairs of 9d1a77e172f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L71-L74

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_mem_fracPairs_of_9d1a77e172f2 {c c' : (Σ k, ι k) → Φ} {γ : K → ℕ} {r q : MRing ι} {y y' : Φ} (hr : IsMultiHomog r γ)
    (hq : IsMultiHomog q γ) (h : aeval c q ≠ 0) (h' : aeval c' q ≠ 0) (e : aeval c r = aeval c q * y)
    (e' : aeval c' r = aeval c' q * y') : (y, y') ∈ fracPairs c c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«mem_fracPairs_of» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_mem_fracPairs_of_9d1a77e172f2
