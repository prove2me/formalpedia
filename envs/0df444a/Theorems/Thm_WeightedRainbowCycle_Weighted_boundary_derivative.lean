-- Prove2me | Theorems.Thm_WeightedRainbowCycle_Weighted_boundary_derivative
-- name    : WeightedRainbowCycle.Weighted.boundary_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:14.224189+00:00
-- url     : https://prove2.me/theorems/bef4d440-fee9-4791-9273-49c74844d02a
-- title:
--   Lemma 4.2 — weighted boundary versus reachability derivative
-- statement:
--   Let $G$ be any finite loopless weighted list graph, let $\ell\ge1$ be an integer, and let $\Delta\ge0$. Suppose every edge has a nonempty color list of size at most $\ell$, every weight is a nonnegative real number, and $\deg_c(u)\le\Delta$ for every vertex $u$ and every ambient color $c$. Fix any vertex $x$ and any $0<q<1$. Include each active color independently with probability $q$ to form $A$. With $U_x(A)$ defined by full-list rainbow walks,
--
--   $$\mathbb E_q\!\left[\frac{|\partial_G U_x(A)|_w}{|U_x(A)|}\right]\le\Delta\left(\frac{q}{(1-q)^{\ell-1}}+\frac{2(1-q)}{q^{\ell-1}}\right)\frac{d}{dq}\mathbb E_q\log|U_x(A)|.$$
--
--   The left side is the expectation of the ratio. The right side differentiates the expected logarithm, with the factor two retained. This lemma relates the operational reachability observable to its weighted boundary and is the source's second supporting lemma. There is no large-degree or large-size condition and no assumption that the graph lacks a rainbow cycle.
--
--   **Formalization Note** The empty walk gives $1\le|U_x(A)|\le|V(G)|$. The expectations are finite polynomials on all real parameters; the displayed inequality is required on the whole open probability interval. No integrability or differentiability hypothesis is supplied as input.
--
--   Differences from the source:
--   - generalization: graphs in the usual simple-graph reading → loopless finite multigraphs with distinct edge identities and length-two cycles allowed; reason: every simple graph embeds unchanged; weighted edge-counting arguments also retain parallel edges
--   - encoding: finite vertices and edges, with an arbitrary color set → finite vertex and edge types, finite edge lists, and an arbitrary ambient color type; reason: these represent every finite input graph and every finite list without restricting colors or real weights
--   - reading: consider the setting of Theorem 1.1 → its structural graph, list, weight, and local color-degree assumptions only; reason: the proof on pp. 10–12 requires neither large N, the lower density bound, nor absence of rainbow cycles
--   - encoding: probabilities and the exponent ell−1 with no stated domain → ell ≥ 1 and 0 < q < 1; reason: all displayed denominators are then defined and natural subtraction matches integer subtraction; ell = 0 admits no edges, so both sides vanish, and at q = 0 or q = 1 a displayed denominator is 0 or 0^0
--   - generalization: the positive Delta regime of the corrected main theorem → Delta ≥ 0 in this lemma; reason: at Delta = 0 all edge weights vanish by nonempty lists and the local bound, so both sides are zero
--   - encoding: independent sampling from the ambient color set → the published Bernoulli polynomial on the finite active colors only; reason: unused colors cannot change any walk, reachable set, boundary, or expectation; derivatives are of that polynomial
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Lemma 4.2, p. 8; proof, pp. 10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_WeightedRainbowCycle_Weighted_Reachability

set_option autoImplicit false

namespace WeightedRainbowCycle.Weighted

/-- Lemma 4.2, p. 8: expectation of the ratio, derivative of expected logarithm. -/
theorem boundary_derivative {V E C : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    (G : Model V E C) (ell : ℕ) (hell : 1 ≤ ell) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hadm : G.Admissible ell delta) (x : V) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    DiffNeighbors.Bias.bernExp q (G.boundaryRatio x) ≤
      delta * (q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1)) *
        deriv (fun p => DiffNeighbors.Bias.bernExp p (G.logReach x)) q := by sorry

end WeightedRainbowCycle.Weighted
