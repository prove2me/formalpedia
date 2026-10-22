-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_lemma_4
-- name    : QMaxCutSDP.Rounding.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:04.385748+00:00
-- url     : https://prove2.me/theorems/e013dbfc-43e3-4b4c-9350-9c60ece5db59
-- title:
--   Lemma 4 — monogamy of entanglement on a star
-- statement:
--   Let $v$ be feasible for (S), let $i$ be a vertex, and let $T$ be a set of $d$ neighbors of $i$. With $v_{ij}=\sum_{a=1}^3v_{ij,a}$, the total unweighted SDP contribution of these edges satisfies
--   $$\frac14\sum_{j\in T}(v_0-v_{ij})\cdot v_0\le\frac{d+1}{2}.$$
--   This limits how much SDP value can concentrate on the edges incident to one vertex.
--
--   **Formalization Note** The finite set $T$ excludes $i$ and contains only graph neighbors, exactly as the source's star graph does.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 7, Lemma 4, eq. (13); proof p. 8

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Lemma 4, p. 7, equation (13), the star monogamy bound. -/
theorem lemma_4 {n N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : SDPVec n N) (hv : IsSFeasible v) (i : Fin n)
    (T : Finset (Fin n)) (hi : i ∉ T) (hT : ∀ j ∈ T, G.Adj i j) :
    (1 / 4 : ℝ) * ∑ j ∈ T, ((v.v0 - vEdge v i j) ⬝ᵥ v.v0) ≤
      ((T.card : ℝ) + 1) / 2 := by sorry
end QMaxCutSDP.Rounding
