-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_edge_arrival_prophet_inequality
-- name    : ProphetMatchingEFGT.edge_arrival_prophet_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:47.109828+00:00
-- url     : https://prove2.me/theorems/5ff80d4d-80ed-4c46-bb3a-7947536f0b17
-- title:
--   A $0.337$-competitive prophet inequality for matching with edge arrivals in general graphs, against the optimum and the ex-ante optimum
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, not necessarily bipartite, whose edge weights $w_e\sim F_e$ are independent with finite means. The edges arrive one by one in an order chosen by an oblivious adversary, and an online policy must decide irrevocably on arrival whether to add the edge to its matching. Then:
--
--   1. **(against the prophet)** there is one online policy, which does not know the order, such that for every arrival order $\sigma$
--   $$\mathbb E_{w,I}[w(I)]\ \ge\ 0.337\cdot\mathbb E_w\Big[\max_{M\text{ matching}}w(M)\Big];$$
--   2. **(against the ex-ante optimum)** for every ex-ante rule $q$ (measurable acceptance probabilities $q_e:\mathbb R\to[0,1]$ with marginals $\mathbb E[q_e(w_e)]$ in $\mathcal F_M$) there is one online policy such that for every arrival order $\sigma$
--   $$\mathbb E_{w,I}[w(I)]\ \ge\ 0.337\cdot\sum_e\mathbb E\big[w_e\,q_e(w_e)\big].$$
--
--   This is the paper's prophet inequality for edge arrivals: Theorem 5.3 combined with the reduction of Theorem 2.3 (§3, p. 10; §5, p. 12) and with §B.2 (p. 25).
--
--   Differences from the source:
--   - reading: the prophet inequality for edge arrival is stated in prose (§3 p.10, §5 p.12, §B.2 p.25), not as a numbered theorem → one statement with clauses (A) against E[w(OPT(w))] and (B) against every ex-ante rule; reason: assembled from Theorem 5.3, Theorem 2.3 and §B.2, as the pages state
--   - generalization: the ex-ante benchmark Σ_e E[w_e | w_e ≥ F_e^{-1}(1 − y_e)]·y_e for the optimal y ∈ FM → c·V(q) for every ex-ante rule q; reason: the threshold rule of the optimal y is one such rule when F_e is atomless (slip 5), so (B) specializes to the source; it also does not presuppose that the argmax exists
--   - reading: no sign condition on weights in the source → none assumed; reason: the source assumes none (slip 7)
--   - encoding: finite expectations, presupposed by the ratio → Integrable coordinates / weights; reason: without it the Bochner integrals are 0 (slip 8)
--   - encoding: 0.337 → 337/1000; reason: the literal constant
--   - encoding: online algorithm with edge arrivals (Definition 2.2, singleton batches) → an OnlinePolicy: decisions from the earlier edges with weights, the current edge and weight, and internal randomness, measurable; ∃ policy ∀ order; reason: the policy cannot see the order or future weights by its type
--   - reading: a graph G = (V, E) (not necessarily bipartite) whose edges are written (uv) (§3, p.9) → a Mathlib SimpleGraph on a finite vertex type: no loops, at most one edge between two vertices; reason: the notation (uv), x_uv and FM's Σ_u y(uv) (p.10) presume one edge per pair of vertices, and (11), (13) use that (uv) is the only u–v edge
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, Theorem 5.3 p. 14 with Theorem 2.3 p. 8, as stated in §3 p. 10, §5 p. 12 and Appendix B.2 p. 25

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_EdgeArrival

open MeasureTheory

namespace ProphetMatchingEFGT

/-- **The 0.337-competitive prophet inequality for matching with edge arrivals in general graphs.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Theorem 5.3 (p. 14) through Theorem 2.3 (p. 8), as stated
in §3, p. 10 ("the 0.337-batched OCRS for edge arrival in Section 5 implies a batched prophet inequality
with competitive ratio 0.337 for edge arrival"), §5, p. 12, and §B.2, p. 25 ("our 0.337-OCRS from
Section 5 implies a 0.337-competitive algorithm for the prophet inequality problem against the ex-ante
optimum").

For every finite simple graph `G` (not necessarily bipartite) and independent integrable edge
weights `w_e ∼ F_e`:
(A) one online policy, which does not know the arrival order, satisfies
`E[w(I)] ≥ 0.337 · E[w(OPT(w))]` under every arrival order;
(B) for every ex-ante rule `q` there is one online policy satisfying
`E[w(I)] ≥ 0.337 · Σ_e E[w_e q_e(w_e)]` under every arrival order.

**Formalization Note.** `0.337` is the literal `337/1000`. The quantifier order is `∃ policy, ∀ σ`. No
sign condition on the weights. -/
theorem edge_arrival_prophet_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Edge G → Measure ℝ)
    [∀ e, IsProbabilityMeasure (F e)] (hF : ∀ e, Integrable (fun t : ℝ => t) (F e)) :
    (∃ P : OnlinePolicy G, ∀ σ : EdgeOrder G, (337 / 1000 : ℝ) * optValue G F ≤ algValue F P σ) ∧
    ∀ q : ExAnteRule G F, ∃ P : OnlinePolicy G, ∀ σ : EdgeOrder G,
      (337 / 1000 : ℝ) * q.value ≤ algValue F P σ := by sorry

end ProphetMatchingEFGT
