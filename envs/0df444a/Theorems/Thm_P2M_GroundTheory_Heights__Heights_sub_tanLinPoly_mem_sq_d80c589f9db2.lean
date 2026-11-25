-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sub_tanLinPoly_mem_sq_d80c589f9db2
-- name    : P2M_GroundTheory_Heights__Heights_sub_tanLinPoly_mem_sq_d80c589f9db2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:28.955716+00:00
-- url     : https://prove2.me/theorems/80076cb9-32ef-4fed-90f7-56860dab8f65
-- title:
--   P2 M Ground Theory Heights  Heights sub tan Lin Poly mem sq d80c589f9db2: P2 M Ground Theory Heights  Heights sub tan Lin Poly mem sq d80c589f9db2
-- statement:
--   The P2 M Ground Theory Heights  Heights sub tan Lin Poly mem sq d80c589f9db2 construction uses the P2 M Ground Theory Heights  Heights sub tan Lin Poly mem sq d80c589f9db2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L76-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L76-L110

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

theorem P2M_GroundTheory_Heights__Heights_sub_tanLinPoly_mem_sq_d80c589f9db2 (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) - tanLinPoly p (polyDiff p f) ∈ RingHom.ker (eval p) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sub_tanLinPoly_mem_sq» := P2M_GroundTheory_Heights__Heights_sub_tanLinPoly_mem_sq_d80c589f9db2
