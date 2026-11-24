-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:59.895666+00:00
-- url     : https://prove2.me/theorems/d53d4861-b243-4c67-a5af-8b61f2bd9b2e
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend sum coord Poly 903079f12110: P2 M Ground Theory Heights  Heights Chow Form Extend sum coord Poly 903079f12110
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend sum coord Poly 903079f12110 construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend sum coord Poly 903079f12110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L107-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L107-L125

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110 (b : Module.Basis β K L) (p : MvPolynomial Y L) :
    ∑ c ∈ coordSupport b p, C (b c) * map (algebraMap K L) (coordPoly (b.coord c) p) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«sum_coordPoly» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
