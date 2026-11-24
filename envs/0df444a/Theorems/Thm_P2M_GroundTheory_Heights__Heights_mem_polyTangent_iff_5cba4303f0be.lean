-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_polyTangent_iff_5cba4303f0be
-- name    : P2M_GroundTheory_Heights__Heights_mem_polyTangent_iff_5cba4303f0be
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:21.485471+00:00
-- url     : https://prove2.me/theorems/f102e0a1-99e7-4102-aa4e-dc8cde02362e
-- title:
--   P2 M Ground Theory Heights  Heights mem poly Tangent iff 5cba4303f0be: P2 M Ground Theory Heights  Heights mem poly Tangent iff 5cba4303f0be
-- statement:
--   The P2 M Ground Theory Heights  Heights mem poly Tangent iff 5cba4303f0be construction uses the P2 M Ground Theory Heights  Heights mem poly Tangent iff 5cba4303f0be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L30-L31

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

theorem P2M_GroundTheory_Heights__Heights_mem_polyTangent_iff_5cba4303f0be (S : Set (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ) :
    v ∈ polyTangent S p ↔ ∀ q ∈ S, dotForm (polyDiff p q) v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_polyTangent_iff» := P2M_GroundTheory_Heights__Heights_mem_polyTangent_iff_5cba4303f0be
