-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_simple_roots_le_65e0c52da8c3
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_simple_roots_le_65e0c52da8c3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:00.424393+00:00
-- url     : https://prove2.me/theorems/76edd1bd-3afb-49b5-ae86-c50943c3866a
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H simple roots le 65e0c52da8c3: P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H simple roots le 65e0c52da8c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H simple roots le 65e0c52da8c3 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H simple roots le 65e0c52da8c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L198-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L198-L206

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

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_simple_roots_le_65e0c52da8c3 {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ)
    (P : Fin n → Polynomial (MvPolynomial (Fin r) ℂ)) (V : Set (Fin n → ℂ))
    (hV : ∀ x ∈ V, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0) :
    dimH {x | x ∈ V ∧ ∀ i, Polynomial.eval (x i)
      ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ≤
      2 * (r : ENNReal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«dimH_simple_roots_le» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_simple_roots_le_65e0c52da8c3
