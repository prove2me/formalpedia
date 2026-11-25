-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_comp_eval__4158a7ce14c2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_comp_eval__4158a7ce14c2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:27.256377+00:00
-- url     : https://prove2.me/theorems/fc196fac-76cc-43b4-b9ef-43140c77ba90
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval comp eval  4158a7ce14c2: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval comp eval  4158a7ce14c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval comp eval  4158a7ce14c2 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval comp eval  4158a7ce14c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L186-L191

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_comp_eval__4158a7ce14c2 {σ n R : Type} [CommRing R] (f : R →+* Φ) (w : n → Φ) (g : σ → MvPolynomial n R)
    (s : MvPolynomial σ ℤ) : aeval (fun p => eval₂ f w (g p)) s = eval₂ f w (aeval g s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«aeval_comp_eval₂» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_comp_eval__4158a7ce14c2
