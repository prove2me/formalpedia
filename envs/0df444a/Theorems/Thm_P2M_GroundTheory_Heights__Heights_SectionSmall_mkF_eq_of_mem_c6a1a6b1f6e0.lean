-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_eq_of_mem_c6a1a6b1f6e0
-- name    : P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_eq_of_mem_c6a1a6b1f6e0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:05.877336+00:00
-- url     : https://prove2.me/theorems/d993d304-03d6-4751-95e1-13d224b56867
-- title:
--   P2 M Ground Theory Heights  Heights Section Small mk F eq of mem c6a1a6b1f6e0: P2 M Ground Theory Heights  Heights Section Small mk F eq of mem c6a1a6b1f6e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Small mk F eq of mem c6a1a6b1f6e0 construction uses the P2 M Ground Theory Heights  Heights Section Small mk F eq of mem c6a1a6b1f6e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L26-L33

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

theorem P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_eq_of_mem_c6a1a6b1f6e0 {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {e m : MvPolynomial (Coord n) ℤ} (h : s.den * e - s.num * m ∈ P.ideal) :
    P.mkF e = s.toFun * P.mkF m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionSmall».«mkF_eq_of_mem» := P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_eq_of_mem_c6a1a6b1f6e0
