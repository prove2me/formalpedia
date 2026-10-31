-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_ex_ante_reduction
-- name    : ProphetMatchingEFGT.ex_ante_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:56.747221+00:00
-- url     : https://prove2.me/theorems/81001d31-aeba-4bbf-9eaf-1f2f85afc884
-- title:
--   §B.2 — a $c$-OCRS gives a $c$-competitive prophet algorithm against the ex-ante optimum
-- statement:
--   Let $G$ be a finite simple graph with independent integrable edge weights $w_e\sim F_e$, let $c\ge0$, and let $q$ be an ex-ante rule: measurable $q_e:\mathbb R\to[0,1]$ with marginals $x_e=\mathbb E[q_e(w_e)]$ forming a point of $\mathcal F_M$. If an OCRS is $c$-selectable for the marginals $x$, then there is a single online policy, which does not know the arrival order, such that for every order $\sigma$
--   $$\mathbb E_{w,I}[w(I)]\ \ge\ c\cdot\sum_e\mathbb E\big[w_e\,q_e(w_e)\big].$$
--
--   For the threshold rule of an ex-ante solution $y$ the right side is $c$ times the paper's ex-ante benchmark $\sum_e\mathbb E[w_e\mid w_e\ge F_e^{-1}(1-y_e)]\,y_e$, which dominates the optimal fractional and integral matchings.
--
--   Differences from the source:
--   - generalization: the realized set R^ex-ante(w, F) = {e | w_e ≥ F_e^{-1}(1 − y_e)} of an ex-ante solution y ∈ FM → any ex-ante rule: e realized with probability q_e(w_e), measurable q_e : ℝ → [0, 1], marginals in FM; reason: for atomless F_e the threshold rule is an ex-ante rule with marginals y and value Σ E[w_e | w_e ≥ F_e^{-1}(1 − y_e)]·y_e; with atoms the threshold set may have Pr > y_e (slip 5) and randomizing at the atom restores the paper's claim
--   - reading: c-OCRS (c a selection probability) → c ≥ 0; reason: for c < 0 every scheme is c-selectable and the claim would fail for negative weights
--   - reading: no sign condition on weights in the source → none assumed; reason: the source assumes none (slip 7)
--   - encoding: Pr[e ∈ I | e ∈ R] ≥ c → product form Pr[A, B] ≥ c·Pr[B] (or the corresponding product of probabilities); reason: the conditional probability is undefined on null events (slip 6); equal where it is defined
--   - encoding: finite expectations, presupposed by the ratio → Integrable coordinates / weights; reason: without it the Bochner integrals are 0 (slip 8)
--   - encoding: prophet inequality algorithm → an online policy seeing only earlier edges with weights, the current edge and weight, and its randomness; measurable decisions; reason: Definition 2.2 with singleton batches
--   - reading: a graph G = (V, E) (not necessarily bipartite) whose edges are written (uv) (§3, p.9) → a Mathlib SimpleGraph on a finite vertex type: no loops, at most one edge between two vertices; reason: the notation (uv), x_uv and FM's Σ_u y(uv) (p.10) presume one edge per pair of vertices, and (11), (13) use that (uv) is the only u–v edge
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, Appendix B.2, p. 25 (ex-ante optimum also defined in §6, p. 18)

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_EdgeArrival

open MeasureTheory

namespace ProphetMatchingEFGT

/-- **§B.2, p. 25: an OCRS gives a prophet inequality against the ex-ante optimum.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, §B.2, p. 25: "Therefore, any c-OCRS with respect to
`R^{ex-ante}(w, F)` gives us a prophet inequality algorithm with competitive ratio c with respect to the
optimal ex-ante solution."

**Formalization Note.** An ex-ante rule `q` (measurable `q_e : ℝ → [0, 1]` with marginals
`x_e = E[q_e(w_e)]` in `FM`) realizes `e` with probability `q_e(w_e)`; the paper's
`R^{ex-ante} = {e | w_e ≥ F_e^{-1}(1 − y_e)}` is the threshold rule. If an OCRS is `c`-selectable for the
marginals `x`, there is one online policy, not knowing the order, whose expected weight is at least
`c · Σ_e E[w_e q_e(w_e)]` under every order. The weights are independent and integrable; `c ≥ 0`. -/
theorem ex_ante_reduction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : Edge G → Measure ℝ) [∀ e, IsProbabilityMeasure (F e)]
    (hF : ∀ e, Integrable (fun t : ℝ => t) (F e)) (c : ℝ) (hc : 0 ≤ c) (q : ExAnteRule G F)
    (A : EdgeOCRS G) (hA : A.IsSelectable q.marginal c) :
    ∃ P : OnlinePolicy G, ∀ σ : EdgeOrder G, c * q.value ≤ algValue F P σ := by sorry

end ProphetMatchingEFGT
