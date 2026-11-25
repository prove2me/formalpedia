-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_sq_of_polyDiff_eq_zero_3e662a2d8d5a
-- name    : P2M_GroundTheory_Heights__Heights_mem_sq_of_polyDiff_eq_zero_3e662a2d8d5a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:38.472359+00:00
-- url     : https://prove2.me/theorems/cfba83ed-c799-4c59-977f-e77aceec3ffc
-- title:
--   P2 M Ground Theory Heights  Heights mem sq of poly Diff eq zero 3e662a2d8d5a: P2 M Ground Theory Heights  Heights mem sq of poly Diff eq zero 3e662a2d8d5a
-- statement:
--   The P2 M Ground Theory Heights  Heights mem sq of poly Diff eq zero 3e662a2d8d5a construction uses the P2 M Ground Theory Heights  Heights mem sq of poly Diff eq zero 3e662a2d8d5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L112-L114

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

theorem P2M_GroundTheory_Heights__Heights_mem_sq_of_polyDiff_eq_zero_3e662a2d8d5a (p : Fin n → ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h0 : eval p f = 0) (h1 : polyDiff p f = 0) : f ∈ RingHom.ker (eval p) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_sq_of_polyDiff_eq_zero» := P2M_GroundTheory_Heights__Heights_mem_sq_of_polyDiff_eq_zero_3e662a2d8d5a
