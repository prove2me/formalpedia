-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_lemma_3
-- name    : QMaxCutSDP.Rounding.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:25.733268+00:00
-- url     : https://prove2.me/theorems/f832aa19-24c9-451f-90fd-29ae0ab6d96c
-- title:
--   Lemma 3 — identities for feasible SDP vectors
-- statement:
--   For a feasible solution of (S), put $v_{ij}=\sum_{a=1}^3v_{ij,a}$. For distinct vertices $i,j$, and for pairwise distinct $i,j,k$ in the last identity,
--   $$\|v_{ij}\|^2=3-2v_{ij}\cdot v_0,\qquad \|v_0+v_{ij}\|^2=4,\qquad v_{ij}\cdot v_{jk}=v_{ik}\cdot v_0.$$
--   The fixed norm of $v_0+v_{ij}$ makes the normalized edge correlation well-defined on actual edges.
--
--   **Formalization Note** Distinctness is explicit because the constraints of (S) impose these relations only on distinct indices.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 7, Lemma 3, eqs. (9)–(12)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Lemma 3, p. 7, equations (10)–(12). -/
theorem lemma_3 {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) :
    (∀ i j : Fin n, i ≠ j →
      (vEdge v i j ⬝ᵥ vEdge v i j = 3 - 2 * (vEdge v i j ⬝ᵥ v.v0)) ∧
      ((v.v0 + vEdge v i j) ⬝ᵥ (v.v0 + vEdge v i j) = 4)) ∧
    (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      vEdge v i j ⬝ᵥ vEdge v j k = vEdge v i k ⬝ᵥ v.v0) := by sorry
end QMaxCutSDP.Rounding
