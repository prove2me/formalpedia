-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsSheetAt_eventuallyEq_5bf3495b137a
-- name    : P2M_GroundTheory_Heights__Heights_IsSheetAt_eventuallyEq_5bf3495b137a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:27.5327+00:00
-- url     : https://prove2.me/theorems/c4b70cda-c301-481a-80f8-2ed6e1778c68
-- title:
--   P2 M Ground Theory Heights  Heights Is Sheet At eventually Eq 5bf3495b137a: P2 M Ground Theory Heights  Heights Is Sheet At eventually Eq 5bf3495b137a
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Sheet At eventually Eq 5bf3495b137a construction uses the P2 M Ground Theory Heights  Heights Is Sheet At eventually Eq 5bf3495b137a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeSheetGramLintegral.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeSheetGramLintegral.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSliceSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGramLintegral
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
open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IsSheetAt_eventuallyEq_5bf3495b137a {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {γ s : (Fin d → ℂ) → Fin n → ℂ}
    (hγ : IsSheetAt J A x γ) (hs : IsSheetAt J A x s) : γ =ᶠ[𝓝 (A *ᵥ x)] s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsSheetAt».«eventuallyEq» := P2M_GroundTheory_Heights__Heights_IsSheetAt_eventuallyEq_5bf3495b137a
