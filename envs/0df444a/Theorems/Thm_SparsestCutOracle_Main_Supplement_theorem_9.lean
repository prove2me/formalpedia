-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_Supplement_theorem_9
-- name    : SparsestCutOracle.Main.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:50:25.830482+00:00
-- url     : https://prove2.me/theorems/4630b325-c2e8-405f-8635-9e5761cc52ff
-- title:
--   Theorem 9 — Subcluster routability gives the exact hierarchy bound
-- statement:
--   Let $G$ be a finite undirected graph on $n\ge2$ vertices with arbitrary nonnegative real capacities. Fix $q^*\ge1$ and $\gamma=1/(500e q^*)$, where $e$ is Euler's constant. Let $P$ be a complete hierarchy of height $L$ with $L\le H(1+\log_2 n)$, for any fixed $H>0$. Suppose every non-leaf level-$i$ cluster $X$ routes every signed zero-sum demand supported on $X$ with pointwise bound $|d|\le\deg_{\partial P_{i+1}}|_X$ inside $G[X]$, with edge-dependent congestion
--   $$
--   \operatorname{con}_e=\frac{\log_2\log_2 n\,(1+f_P(X))}{\gamma}+11f_P(X_e^{(i+1)})
--   $$
--   on internal edges and zero elsewhere. Here $f_P$ is one at the root and the base-two logarithm of the parent-to-child cardinality ratio elsewhere; $X_e^{(i+1)}$ is the smaller endpoint cluster at level $i+1$.
--
--   Then $P$ is a congestion approximator with the exact approximation guarantee
--   $$
--   \frac{2\log_2\log_2 n\,(L+\log_2 n)}{\gamma}+22\log_2 n.
--   $$
--   Thus every demand passing all the hierarchy's per-cluster cut tests routes within this scalar congestion. Connectivity is not an added hypothesis; demands remain signed and capacities need not be integral or bounded below by one. This is the routing theorem used by the construction in Theorem 2.
--
--   Differences from the source:
--   - reading: page 44 writes deg_{∂C}(X) using the multilevel collection boundary, while the proof on page 45 uses deg_{∂P_i}(X) → the tests are |d(X)|≤cap(X,V∖X) at every level; reason: this is exactly the proof’s per-partition boundary degree and necessary cut condition; the literal multilevel union-degree version fails on the four-vertex weighted-path example in MODERATION_NOTES.md
--   - reading: unscripted combinatorial logarithms and explicit log₂ cardinality ratios → base-two logarithms throughout the exact §8.2 formula; reason: the page-47 telescoping calculation uses the same base for f_P and log n; no constant conversion is hidden
--   - encoding: finite hierarchy with nonempty clusters and logarithmic height L → level-tagged list of distinct partitions on Fin n, n≥2, and arbitrary H>0 with L≤H(1+log₂ n); reason: tags preserve persistent clusters; positive cardinalities and n≥2 give defined logarithms; H is universally quantified and L stays explicit
--   - encoding: flows in G[X] with one congestion entry for each edge → oriented signed edge-list flows with separate capacity bounds, aggregated using the published Flow/netFlow; reason: this preserves parallel edges, zero-capacity edges, induced support and every real nonnegative capacity
--   - generalization: page 7’s standing connected-graph convention and zero diagonal capacity → arbitrary graphs represented by the published nonnegative edge list, including disconnected graphs and harmless loops; reason: zero-boundary clusters have d(X)=0 by their cut test, so the level demands can be set to zero there; loops contribute neither divergence nor boundary and can carry zero flow; the statement specializes to every source instance
--   - generalization: a complete hierarchy of logarithmic height → any finite complete hierarchy, with an arbitrary positive H bounding its height by H(1+log₂ n); reason: H is universally quantified after n, so it imposes no uniform height restriction; the routing argument on pages 45–47 keeps L explicit and works for every finite height, including every logarithmic-height source hierarchy
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 45, Theorem 9

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Supplement_Hierarchy

namespace SparsestCutOracle.Main.Supplement

/-- Theorem 9, p.45: exact constants, base-two combinatorial logs and level-tagged nodes.
The height constant is arbitrary, fixed before the hierarchy; L stays explicit. -/
theorem theorem_9 (n : ℕ) (hn : 2 ≤ n) (G : Graph n) (q H : ℝ)
    (hq : 1 ≤ q) (hH : 0 < H) (P : Hierarchy n) (hP : Complete P)
    (hheight : (P.length : ℝ) ≤ H * (1 + Real.logb 2 n))
    (hrouting : SubclusterRoutable G P (1 / (500 * Real.exp 1 * q))) :
    CongestionApproximator G P
      (2 * Real.logb 2 (Real.logb 2 n) * (P.length + Real.logb 2 n) /
        (1 / (500 * Real.exp 1 * q)) + 22 * Real.logb 2 n) := by sorry

end SparsestCutOracle.Main.Supplement
