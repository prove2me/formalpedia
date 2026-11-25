-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f
-- name    : P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:54.094908+00:00
-- url     : https://prove2.me/theorems/556a0267-593c-46bb-a143-69363e0c6d7f
-- title:
--   P2 M Ground Theory Heights  Heights is Weighted Homogeneous of mul left 246006f8ee8f: P2 M Ground Theory Heights  Heights is Weighted Homogeneous of mul left 246006f8ee8f
-- statement:
--   The P2 M Ground Theory Heights  Heights is Weighted Homogeneous of mul left 246006f8ee8f construction uses the P2 M Ground Theory Heights  Heights is Weighted Homogeneous of mul left 246006f8ee8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L105-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L105-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}
variable [IsDomain R]

theorem P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f {p q : MvPolynomial σ R} {m : ℕ}
    (hpq : IsWeightedHomogeneous w (p * q) m) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a, IsWeightedHomogeneous w p a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isWeightedHomogeneous_of_mul_left» := P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f
