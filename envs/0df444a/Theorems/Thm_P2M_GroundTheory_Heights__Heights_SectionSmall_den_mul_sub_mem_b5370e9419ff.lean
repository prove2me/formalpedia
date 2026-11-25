-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_den_mul_sub_mem_b5370e9419ff
-- name    : P2M_GroundTheory_Heights__Heights_SectionSmall_den_mul_sub_mem_b5370e9419ff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:15.30007+00:00
-- url     : https://prove2.me/theorems/9ed7e96d-3353-4837-887d-3d28c03f18c8
-- title:
--   P2 M Ground Theory Heights  Heights Section Small den mul sub mem b5370e9419ff: P2 M Ground Theory Heights  Heights Section Small den mul sub mem b5370e9419ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Small den mul sub mem b5370e9419ff construction uses the P2 M Ground Theory Heights  Heights Section Small den mul sub mem b5370e9419ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall

theorem P2M_GroundTheory_Heights__Heights_SectionSmall_den_mul_sub_mem_b5370e9419ff {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q : MvPolynomial (Coord n) ℤ} (h : P.mkF p = s.toFun * P.mkF q) :
    s.den * p - s.num * q ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionSmall».«den_mul_sub_mem» := P2M_GroundTheory_Heights__Heights_SectionSmall_den_mul_sub_mem_b5370e9419ff
