-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_eq_19
-- name    : QMaxCutSDP.Rounding.eq_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:19.520362+00:00
-- url     : https://prove2.me/theorems/4275f4ea-f3d9-4754-9131-a71929ac7c51
-- title:
--   Equation (19) — SDP edge contribution in terms of γ
-- statement:
--   For a feasible vector solution of (S) and distinct vertices $i,j$, the normalized correlation $\gamma_{ij}$ and the edge's SDP contribution satisfy
--   $$\gamma_{ij}=-\frac{1+v_{ij}\cdot v_0}{2},\qquad (v_0-v_{ij})\cdot v_0=2(1+\gamma_{ij}).$$
--   The identity expresses the SDP objective in the same one-edge parameter used to choose the circuit angle.
--
--   **Formalization Note** Feasibility and distinctness make the normalization denominator $2$, by Lemma 3; no division-by-zero case is imported into the claim.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 11, proof of Theorem 1, eq. (19)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, proof of Theorem 1, p. 11, equation (19) and its consequence. -/
theorem eq_19 {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v)
    (i j : Fin n) (hij : i ≠ j) :
    gammaE v i j = -(1 + vEdge v i j ⬝ᵥ v.v0) / 2 ∧
    (v.v0 - vEdge v i j) ⬝ᵥ v.v0 = 2 * (1 + gammaE v i j) := by sorry
end QMaxCutSDP.Rounding
