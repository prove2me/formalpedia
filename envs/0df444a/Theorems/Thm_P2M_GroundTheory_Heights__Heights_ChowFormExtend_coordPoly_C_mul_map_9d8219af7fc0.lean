-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:55.85201+00:00
-- url     : https://prove2.me/theorems/c3cd7e1b-9813-463f-b007-ce09a566a4e2
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly C mul map 9d8219af7fc0: P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly C mul map 9d8219af7fc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly C mul map 9d8219af7fc0 construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend coord Poly C mul map 9d8219af7fc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L96-L100

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0 (φ : L →ₗ[K] K) (a : L) (q : MvPolynomial Y K) :
    coordPoly φ (C a * map (algebraMap K L) q) = C (φ a) * q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«coordPoly_C_mul_map» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
