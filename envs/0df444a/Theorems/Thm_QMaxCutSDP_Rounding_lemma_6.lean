-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_lemma_6
-- name    : QMaxCutSDP.Rounding.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:26.846629+00:00
-- url     : https://prove2.me/theorems/4f4d9ee3-bd2e-4279-b67a-8c93b9e2ef6e
-- title:
--   Lemma 6 — lower bound on one circuit edge's energy
-- statement:
--   Let $z$ be a bit string and apply the paper's edge-gate circuit with symmetric parameters $0\le\theta_{ij}\le\pi/4$ on every edge. Put $A_{ij}=\prod_{k\in N(i)\setminus\{j\}}\cos(2\theta_{ik})$ and $B_{ij}=\prod_{k\in N(j)\setminus\{i\}}\cos(2\theta_{kj})$. For the output state $|\phi(\theta)\rangle$ and any edge $(i,j)$,
--   $$\langle\phi(\theta)|4H_{ij}|\phi(\theta)\rangle\ge\begin{cases}1+\sin(2\theta_{ij})(A_{ij}+B_{ij})+A_{ij}B_{ij},&z_i\ne z_j,\\0,&z_i=z_j.\end{cases}$$
--   This isolates the effect of neighboring gates on an edge's energy.
--
--   **Formalization Note** The printed lemma assumes only nonnegative angles, but its bound fails above $\pi/4$. Algorithm 1 always produces angles in $[0,\pi/4]$, so the added upper bound covers its use. Symmetry states explicitly that each undirected edge has one parameter.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 10, Lemma 6, eq. (15); proof pp. 15–17

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Lemma 6, p. 10, equation (15), with the necessary angle range. -/
theorem lemma_6 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : BitString n) (θ : Fin n → Fin n → ℝ)
    (hθsym : ∀ i j, G.Adj i j → θ i j = θ j i)
    (hθrange : ∀ i j, G.Adj i j → 0 ≤ θ i j ∧ θ i j ≤ Real.pi / 4)
    (i j : Fin n) (hij : G.Adj i j) :
    (if z i ≠ z j then
      1 + Real.sin (2 * θ i j) * (neighborProduct G θ i j + neighborProduct G θ j i) +
        neighborProduct G θ i j * neighborProduct G θ j i
     else (0 : ℝ)) ≤
    4 * (star (outState G z θ) ⬝ᵥ (hEdge i j *ᵥ outState G z θ)).re := by sorry
end QMaxCutSDP.Rounding
