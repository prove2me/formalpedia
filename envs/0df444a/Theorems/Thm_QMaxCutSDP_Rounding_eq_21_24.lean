-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_eq_21_24
-- name    : QMaxCutSDP.Rounding.eq_21_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:10.783589+00:00
-- url     : https://prove2.me/theorems/42084e05-a1e8-4c39-9d04-636a2a9f23ce
-- title:
--   Equations (21)–(24) — positive-neighbor sum and circuit-product bounds
-- statement:
--   In a feasible solution of (S), let $N(i)^+$ be the neighbors $k$ of $i$ with $\gamma_{ik}>0$. Equations (21)–(22) bound the total positive correlation at every vertex:
--   $$\sum_{k\in N(i)^+}\gamma_{ik}\le1.$$
--   For an edge $(i,j)$ in the proof's case $0\le\gamma_{ij}\le1$, equations (23)–(24) then give
--   $$A_{ij},B_{ij}\ge\exp[-0.041(1-\gamma_{ij})],$$
--   where $A_{ij}$ and $B_{ij}$ are the products of neighboring $\cos(2\theta)$ factors defined in Lemma 6 and the angles come from Algorithm 1. These estimates turn the local circuit-energy bound into an expression in one scalar correlation.
--
--   **Formalization Note** The summand in the paper's display (21) says $v_{ij}$ inside a sum over $k$; it is read as $v_{ik}$, consistent with the next line and the monogamy calculation. The last two inequalities are stated in the proof's nonnegative-correlation case.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 12, proof of Theorem 1, eqs. (21)–(24)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, proof of Theorem 1, p. 12, equations (21)–(24). -/
theorem eq_21_24 {n N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : SDPVec n N) (hv : IsSFeasible v) :
    (∀ i : Fin n, ∑ k ∈ positiveNeighbors G v i, gammaE v i k ≤ 1) ∧
    (∀ i j : Fin n, G.Adj i j → 0 ≤ gammaE v i j → gammaE v i j ≤ 1 →
      Real.exp (-alpha0 * (1 - gammaE v i j)) ≤
        neighborProduct G (thetaE v) i j ∧
      Real.exp (-alpha0 * (1 - gammaE v i j)) ≤
        neighborProduct G (thetaE v) j i) := by sorry
end QMaxCutSDP.Rounding
