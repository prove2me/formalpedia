-- Prove2me | Theorems.Thm_QGraphColl_lemma_3_3
-- name    : QGraphColl.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:14.971964+00:00
-- url     : https://prove2.me/theorems/dd98930b-62ef-4e36-a07f-d26f03cc02bd
-- title:
--   Lemma 3.3 — comparison with the marked set: $\sum_u(\ell_u(S)-\ell_u(M))^2\le2\sum_v e_v(1[v\in S]-x_v)$
-- statement:
--   Let $G$ be a graph on $V$, $x$ an input with marked set $M$, $z\in\mathbb R^V$, and $S\subseteq V$ with $\psi_z(S)\le\psi_z(M)$. Then
--   $$\sum_u\big(\ell_u(S)-\ell_u(M)\big)^2\le2\sum_v e_v\big(\mathbf 1[v\in S]-x_v\big),\qquad e_v=z_v-\sum_w c_{vw}x_w.\qquad(3.1)$$
--
--   The least-squares minimizer is compared with the unknown marked set without knowing it: the error of its neighbourhood counts is controlled by the errors $e_v$ of the sampled common-neighbour sums.
--
--   Differences from the source: none.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 3.3 and (3.1), p.16

import Mathlib
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol

namespace QGraphColl

/-- **Lemma 3.3** (Comparison with the marked set; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.16). Let `S ⊆ V(G)` satisfy
`ψ_z(S) ≤ ψ_z(M)`. Then
`∑_u (ℓ_u(S) − ℓ_u(M))² ≤ 2 ∑_v e_v (1[v ∈ S] − x_v)`, where `e_v = z_v − ∑_w c_vw x_w` (3.1).

**Formalization Note.** `z` is an arbitrary real vector indexed by the vertices (the paper's
sampled common-neighbour sums; the comparison is deterministic). `x_v` is read as `1` or `0`. -/
theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → Bool)
    (z : V → ℝ) (S : Finset V) (h : psi G z S ≤ psi G z (marked x)) :
    ∑ u, ((ell G S u : ℝ) - (ell G (marked x) u : ℝ)) ^ 2 ≤
      2 * ∑ v, (z v - ∑ w, (cn G v w : ℝ) * (if x w = true then 1 else 0)) *
        ((if v ∈ S then 1 else 0) - (if x v = true then 1 else 0)) := by sorry

end QGraphColl
