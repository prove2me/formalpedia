-- Prove2me | Theorems.Thm_RandomOrderCRS_theorem_3_all_inputs
-- name    : RandomOrderCRS.theorem_3_all_inputs
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:03.95243+00:00
-- url     : https://prove2.me/theorems/43f73849-ed0b-4405-8912-5a8d7726259f
-- title:
--   Theorem 3 with Lemma 1 — a $c^*$-selectable RCRS for every graph
-- statement:
--   For every finite simple graph $G=(V,E)$ and every fractional matching $x$ of $G$, there is a random-order contention resolution scheme that selects each edge $e$ with probability at least $c^*x_e$, where
--
--   $$c^*=\frac{e^2-4e^3+e^4+20e-22}{4e^2}\ge0.474035.$$
--
--   This is the entry "Any RCRS, General Graphs, $\ge0.474$" of Table 1 of the paper. The paper reports it as an improvement on the best known guarantee, even for offline contention resolution on general graphs.
--
--   The scheme sees, at each arrival, only its private randomness, the past arrivals with their states, and the current edge and state. It may depend on $(G,x)$. It is not Algorithm 2 on $G$ in general: it simulates the gadget edges of the 1-regular reduction.
--
--   Differences from the source:
--   - encoding: a sequential scheme with a uniformly random order → `Policy` (finite seed, decision on history, current edge and state), `run`, and the average of `selProb` over all $|E|!$ orders; reason: finite seeds lose no generality, since a scheme is a mixture of finitely many deterministic rules
--   - reading: the simulation in the reduction may reuse the real arrival times (ec15) → a `Policy` sees only the order and the states; reason: this is the stronger of the two readings of the model on p.3 and ec15
--   - encoding: graphs $G=(V,E)$ → finite simple graphs `SimpleGraph V`; reason: the paper's edges are pairs $(u,v)$, and $f^c$ is defined for them
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Theorem 3 and Lemma 1, p.17; Table 1, p.4

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Policy
import Definitions.Def_RandomOrderCRS_Attenuation

namespace RandomOrderCRS

/-- Theorem 3 with Lemma 1, MacRury, Ma & Grammel, arXiv:2209.07520v2, p.17; Table 1, p.4: "Any
RCRS", "General Graphs", "≥ 0.474". For every finite simple graph `G` and every fractional matching
`x` of `G` there is a random-order contention resolution scheme that selects each edge `e` with
probability at least `c* x_e`, where `c* = (e²−4e³+e⁴+20e−22)/(4e²) ≥ 0.474035`.

**Formalization Note.** The constant is fixed before `G`. The scheme `π` may depend on `(G, x)`,
as the paper's CRS "is passed G and x as input" (p.3). A `Policy` sees only its private seed, the
past arrivals with their states, and the current edge and state. So this is not Algorithm 2 on `G`
in general: for a graph that is not 1-regular the scheme simulates gadget edges. -/
theorem theorem_3_all_inputs :
    (0.474035 : ℝ) ≤ cStar ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (x : Sym2 V → ℝ), IsFractionalMatching G x →
      ∃ π : Policy G, IsRCRSelectable G π x cStar := by sorry

end RandomOrderCRS
