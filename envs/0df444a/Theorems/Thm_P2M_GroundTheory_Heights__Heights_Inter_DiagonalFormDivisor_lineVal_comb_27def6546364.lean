-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_lineVal_comb_27def6546364
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_lineVal_comb_27def6546364
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:19.479838+00:00
-- url     : https://prove2.me/theorems/8623c0e9-bd3c-41e4-937f-d4b753df9afb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line Val comb 27def6546364: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line Val comb 27def6546364
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line Val comb 27def6546364 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor line Val comb 27def6546364 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L151-L155

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_lineVal_comb_27def6546364 (e : Module.Basis (Fin 2) Ω E) (φ₀ φ₁ : E →ₗ[Ω] Ω) (c₀ c₁ : Ω) (b : Φ) :
    T.lineVal e (c₀ • φ₀ + c₁ • φ₁) b =
      algebraMap Ω Φ c₀ * T.lineVal e φ₀ b + algebraMap Ω Φ c₁ * T.lineVal e φ₁ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«lineVal_comb» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_lineVal_comb_27def6546364
