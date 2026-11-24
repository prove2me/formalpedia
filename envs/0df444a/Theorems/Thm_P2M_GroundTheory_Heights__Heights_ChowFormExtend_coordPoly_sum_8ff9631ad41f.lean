-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:12.150458+00:00
-- url     : https://prove2.me/theorems/dbd67fbd-0293-413f-8d08-0e9fa1c52afa
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly sum 8ff9631ad41f: P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly sum 8ff9631ad41f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly sum 8ff9631ad41f construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly sum 8ff9631ad41f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L127-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
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
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
variable {β : Type*} [DecidableEq β]

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f (b : Module.Basis β K L) (S : Finset β) (h : β → MvPolynomial Y K) (c : β) :
    coordPoly (b.coord c) (∑ c' ∈ S, C (b c') * map (algebraMap K L) (h c')) =
      if c ∈ S then h c else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«coordPoly_sum» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
