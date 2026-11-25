-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_scale_d6b95e793f4c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_scale_d6b95e793f4c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:51.84873+00:00
-- url     : https://prove2.me/theorems/29902bc8-774c-5bec-91cd-1f653ccb7c02
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval scale d6b95e793f4c: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval scale d6b95e793f4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval scale d6b95e793f4c construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor aeval scale d6b95e793f4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L98-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L98-L106

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_scale_d6b95e793f4c (u : K → Φ) (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    aeval (fun p => u p.1 * c p) s = (∏ k, u k ^ β k) * aeval c s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«aeval_scale» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_scale_d6b95e793f4c
