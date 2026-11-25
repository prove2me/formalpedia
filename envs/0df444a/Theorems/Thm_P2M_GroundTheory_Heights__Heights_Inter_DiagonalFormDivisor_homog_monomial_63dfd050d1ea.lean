-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_homog_monomial_63dfd050d1ea
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_homog_monomial_63dfd050d1ea
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:55.44686+00:00
-- url     : https://prove2.me/theorems/ecdb87ee-f45a-4663-983a-f868571fec67
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor homog monomial 63dfd050d1ea: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor homog monomial 63dfd050d1ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor homog monomial 63dfd050d1ea construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor homog monomial 63dfd050d1ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L193-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L193-L202

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
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_homog_monomial_63dfd050d1ea (i : ι) (l : ν) (k : κ) (n₁ n₂ n₃ n₄ : ℕ) :
    IsMultiHomog (X ⟨.base, i⟩ ^ n₁ * X ⟨.det, l⟩ ^ n₂ * X ⟨.line0, k⟩ ^ n₃ * X ⟨.line1, k⟩ ^ n₄ :
      MRing (T.wwIdx ι ν κ)) (blockScale n₁ n₂ n₃ n₄) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«homog_monomial» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_homog_monomial_63dfd050d1ea
