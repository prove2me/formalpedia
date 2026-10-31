-- Prove2me | Theorems.Thm_TSPSDPGap_simplicial_tsp_opt
-- name    : TSPSDPGap.simplicial_tsp_opt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:11.814732+00:00
-- url     : https://prove2.me/theorems/c62dca83-48b7-4530-9a2d-dfaf09812890
-- title:
--   Proof of Theorem 4.1 — the $(n+1)$-vertex simplicial instance is metric with $\mathrm{OPT}_{\mathrm{TSP}}=g$
-- statement:
--   Let $g\ge2$ be even with $g\mid n$ and $g<n$. Consider the instance on $n+1$ vertices with $g$ groups, where groups $2,\dots,g$ have $n/g$ vertices and group $1$ has $n/g+1$ (the extra vertex being an arbitrary vertex $s$), cost $0$ inside a group and $1$ between groups. Then the costs are metric and
--   $$
--   \mathrm{OPT}_{\mathrm{TSP}}=g,
--   $$
--   since each group must be visited at least once.
--
--   This is the numerator of the ratio that proves Theorem 4.1 (with $g=2z$).
--
--   Differences from the source:
--   - generalization: the extra vertex is vertex 1 → the extra vertex is any s ∈ Fin (n + 1); reason: a relabelling of the same instance; s = 0 is the paper's labelling
--   - generalization: OPT_TSP = g on the (n + 1)-vertex instance (p.27) → IsMetricCost of the instance and tspOpt = g; reason: the metric conjunct is p.14's "these instances are metric", needed for the instance to lie in 𝒟; dropping it gives the printed claim
--   - encoding: OPT_TSP; metric and symmetric costs → MetricTSP.tspOpt (minimum over cyclic orderings); MetricTSP.IsMetricCost (symmetric, zero diagonal, triangle inequality); reason: the published metric-TSP model; same notions
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, proof of Theorem 4.1, p.27 ("OPT_TSP = g = 2z"); metric instances, p.14

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_TSPSDPGap_simplicialCostExt

namespace TSPSDPGap

/-- **Proof of Theorem 4.1: the extended simplicial instance is metric and has `OPT_TSP = g`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, proof of Theorem 4.1, p.27: "Note also that OPT_TSP = g = 2z since each group of
vertices must be visited at least once"; and p.14: "Note also that these instances are metric".

For the instance on `n + 1` vertices with `g` groups (group 1 holding the extra vertex `s`),
the costs are metric and the optimal tour costs exactly `g`.

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** The instance is `simplicialCostExt g n s` for any choice `s` of the extra
vertex (the paper takes vertex 1, i.e. `s = 0`); `MetricTSP.IsMetricCost` and
`MetricTSP.tspOpt` are the published metric-TSP definitions. -/
theorem simplicial_tsp_opt (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) (s : Fin (n + 1)) :
    MetricTSP.IsMetricCost (simplicialCostExt g n s) ∧
      MetricTSP.tspOpt (simplicialCostExt g n s) = g := by sorry

end TSPSDPGap
