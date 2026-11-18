-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_coefficient_good_event
-- name    : SYKFastMix.FastMixing.coefficient_good_event
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:52:55.568881+00:00
-- url     : https://prove2.me/theorems/5b29b6ae-2510-42e1-b38e-32b6132b59f1
-- title:
--   A common disorder event for all Taylor coefficient bounds
-- statement:
--   Let $Q$ be an SYK model on an even number $N\ge4$ of Majoranas with coupling scale $J>0$ and the specified product Gaussian disorder law. There is a measurable event $A$ satisfying
--
--   $$\mathbb P(A)\ge1-2e^{-N}$$
--
--   such that each disorder realization in $A$ obeys the simultaneous estimates
--
--   $$\|H\|\le 2JN,\qquad \|F_m\|\le(133J)^m\quad(m\ge1),\qquad \|M_m\|\le(m+1)(133J)^{m+1}\quad(m\ge0).$$
--
--   Here $F_m$ and $M_m$ are the Taylor coefficients of the fermionic Jacobian and block operator in equation (5.7). This event supplies the coefficient control used to obtain uniform imaginary-time bounds.
-- source:
--   Cai, Zhan, Zlokapa, Fast mixing of the SYK model at high temperatures, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1050.pdf, pp.27-28, proof of Corollary 15, Eqs. (5.30)-(5.34), especially (5.32).

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
open SYKFastMix.FastMixing

theorem SYKFastMix.FastMixing.coefficient_good_event {N : ℕ} (Q : Model N) :
  ∃ A : Set (Disorder N), MeasurableSet A ∧
    ENNReal.ofReal (1 - 2 * Real.exp (-(N : ℝ))) ≤ disorderLaw Q A ∧
    ∀ w ∈ A, SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N ∧
      (∀ m : ℕ, 1 ≤ m → SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133 * Q.J)^m) ∧
      (∀ m : ℕ, SYKEdge.opNorm (mCoefficient Q w m) ≤ (m+1) * (133 * Q.J)^(m+1)) := by sorry
