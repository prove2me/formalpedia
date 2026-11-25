-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_polyTangent_eq_of_subset_bc9afe14a4f4
-- name    : P2M_GroundTheory_Heights__Heights_polyTangent_eq_of_subset_bc9afe14a4f4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:29.737431+00:00
-- url     : https://prove2.me/theorems/fecaa58e-2430-472b-a41c-fd7af5219fec
-- title:
--   P2 M Ground Theory Heights  Heights poly Tangent eq of subset bc9afe14a4f4: P2 M Ground Theory Heights  Heights poly Tangent eq of subset bc9afe14a4f4
-- statement:
--   The P2 M Ground Theory Heights  Heights poly Tangent eq of subset bc9afe14a4f4 construction uses the P2 M Ground Theory Heights  Heights poly Tangent eq of subset bc9afe14a4f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L33-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_polyTangent_eq_of_subset_bc9afe14a4f4 (S T : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hST : S ⊆ T) (h : ∀ f ∈ T, polyDiff p f ∈ Submodule.span ℂ (polyDiff p '' S)) :
    polyTangent S p = polyTangent T p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«polyTangent_eq_of_subset» := P2M_GroundTheory_Heights__Heights_polyTangent_eq_of_subset_bc9afe14a4f4
