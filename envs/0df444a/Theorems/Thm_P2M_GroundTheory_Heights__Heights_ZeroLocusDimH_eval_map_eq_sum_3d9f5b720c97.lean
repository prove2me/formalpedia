-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_eq_sum_3d9f5b720c97
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_eq_sum_3d9f5b720c97
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:37.979805+00:00
-- url     : https://prove2.me/theorems/fe4bcffd-78ac-47de-8818-1a094f6fecae
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H eval map eq sum 3d9f5b720c97: P2 M Ground Theory Heights  Heights Zero Locus Dim H eval map eq sum 3d9f5b720c97
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H eval map eq sum 3d9f5b720c97 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H eval map eq sum 3d9f5b720c97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L116-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_eq_sum_3d9f5b720c97 {r : ℕ} (Q : Polynomial (MvPolynomial (Fin r) ℂ)) (y : Fin r → ℂ) (t : ℂ) :
    Polynomial.eval t (Q.map (MvPolynomial.eval y)) =
      ∑ k ∈ range (Q.natDegree + 1), MvPolynomial.eval y (Q.coeff k) * t ^ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«eval_map_eq_sum» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_eq_sum_3d9f5b720c97
