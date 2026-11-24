-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:18.762436+00:00
-- url     : https://prove2.me/theorems/0bfe2431-649e-4a6b-a1c6-98894212aa81
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly mem of mem map 75eab8a0118b: P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly mem of mem map 75eab8a0118b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly mem of mem map 75eab8a0118b construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly mem of mem map 75eab8a0118b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L134-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L134-L164

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b (b : Module.Basis β K L) (T : Ideal (MvPolynomial Y K))
    {p : MvPolynomial Y L} (hp : p ∈ T.map (map (algebraMap K L))) (c : β) :
    coordPoly (b.coord c) p ∈ T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«coordPoly_mem_of_mem_map» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
