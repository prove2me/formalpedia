-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_potential
-- name    : PaceSSSP517.Certified.potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:55.729627+00:00
-- url     : https://prove2.me/theorems/b92177bc-c841-45a8-be36-4c6cf9284c1d
-- title:
--   Lemma 3.5 — Potential identity and both bounds
-- statement:
--   For every reachable pre-Pass-A state of round $r$, let $Q^{(r)}$ be the total edge weight. Then deterministically
--
--   $$Q^{(r)}=\sum_eq_e^{(r)}=m\prod_{j<r,\ j\ \mathrm{not\ bulk}}(1+c_j)
--   \le mr\exp\!\left(\frac{\varepsilon(r-1)}{10k}\right)
--   \exp\!\left(n^{1/k}\sum_{j<r}\rho_j\right).$$
--
--   Each earlier non-bulk round has $\mu_j\ge1+n^{1/k}$. If $\rho_j\le2\theta$ in every earlier non-bulk round, both sharper conclusions hold:
--
--   $$c_j\le\max\{1/j,\varepsilon/(5k)\}\quad(j<r,\ j\ \mathrm{not\ bulk}),\qquad
--   Q^{(r)}\le mr\exp\!\left(\frac{\varepsilon(r-1)}{5k}\right).$$
--
--   The sum in the general bound includes every earlier round, as on the page; the product excludes bulk rounds. The first round has an empty product equal to one, so $Q^{(1)}=m$. This result retains the full deterministic identity and general bound as well as the two consequences of the sampling event.
--
--   Differences from the source:
--   - encoding: finite undirected positive-real weighted graphs and one-based rounds → Fin n vertices, each edge stored once with its smaller endpoint first, and list position j-1 for round j; source vertex s₀ and real sample budget s; reason: these are bijective naming and indexing conventions; no parallel edges or weight restriction is added
--   - encoding: compute exact source distances and a shortest-path tree of the observed subgraph → n-1 synchronous local Bellman–Ford relaxations and the least numbered tight predecessor at each non-source vertex; reason: this fixes a permitted deterministic tie rule using only the observed subgraph; its exactness and finite path realization are proof obligations, not run assumptions
--   - encoding: Q is the sum of current weights and rho is the fraction defined in each round → Qat and rhoAt reconstruct these quantities from finite prefix products and sums; reason: the transition stores only profiles and scalar multipliers; equality of the stored Q with the sum is explicitly asserted
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 7, Lemma 3.5; p. 18, Appendix A.4

import Definitions.Def_PaceSSSP517_Certified_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified

/-- Lemma 3.5, p.7; proof A.4 p.18. All three deterministic clauses and
both sharpened conclusions, with the elevated n^(1/k) exponent preserved. -/
theorem potential
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n))
    (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε))
    (a : State n) (ha : PreHistory G H s₀ k ε a) :
    let ts := a.rounds
    let r := ts.length + 1
    a.Q = ∑ e ∈ G.edges, edgeWeight G a e ∧
    a.Q = G.edges.card * ∏ j ∈ (past (r - 1)).filter (fun j => (roundAt ts j).bulk = false),
      (1 + (roundAt ts j).c) ∧
    a.Q ≤ G.edges.card * (r : ℝ) * Real.exp (ε * (r - 1) / (10 * k)) *
      Real.exp (root n k * ∑ j ∈ past (r - 1), rhoAt G ts j) ∧
    (∀ j ∈ past (r - 1), (roundAt ts j).bulk = false →
      1 + root n k ≤ (roundAt ts j).mu) ∧
    ((∀ j ∈ past (r - 1), (roundAt ts j).bulk = false → rhoAt G ts j ≤ 2 * theta n k ε) →
      (∀ j ∈ past (r - 1), (roundAt ts j).bulk = false →
        (roundAt ts j).c ≤ max (1 / (j : ℝ)) (ε / (5 * k))) ∧
      a.Q ≤ G.edges.card * (r : ℝ) * Real.exp (ε * (r - 1) / (5 * k))) := by sorry

end PaceSSSP517.Certified
