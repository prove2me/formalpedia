-- Prove2me | Theorems.Thm_PivotADO_OneHop_theorem_1
-- name    : PivotADO.OneHop.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:20.208854+00:00
-- url     : https://prove2.me/theorems/769684a5-7886-4a5d-b7bb-95a6fc4f8f0b
-- title:
--   Theorem 1 — space m^(1+2/(k+1))/(r² log n) under Conjecture 1
-- statement:
--   Assume the constant-degree girth conjecture (Conjecture 1), which remains open. For every real $k\ge1$, there are an integer $\Delta$ and positive real constants $a,b,\kappa$ such that, for every size threshold $N$, there exist $n\ge N$ and a simple undirected unweighted graph $G$ on $n$ vertices, with $m=|E(G)|$, satisfying maximum degree at most $\Delta$, $an\le m\le bn$, and the following bound for every integer $r\ge1$ and every $r$-pivot 1-hop $k$-stretch oracle $(H,w,\mathcal P)$ for that same $G$:
--
--   $$\kappa m^{1+2/(k+1)}\le r^2(\log n)|E_H|.$$
--
--   All four constants are chosen before $N,n,G$; the graph is chosen before $r$ and the oracle. The exponent uses a real power and the logarithm is natural. There is no upper bound on $r$ and no connectedness assumption on $G$. The minimum in the oracle includes the costs of both pivot jumps and the central hop, and its space counts all stored unordered edges. This is the paper's conditional main theorem at full strength; it does not assert or prove Conjecture 1.
--
--   Differences from the source:
--   - generalization: finite nonnegative edge weights → edge weights in ℝ≥0∞, including infinity; reason: an infinite-weight stored edge is counted and cannot improve any finite query; finite-weight oracles are included
--   - encoding: constant-degree n-vertex graphs with m = Θ(n), arbitrarily large n, requiring Ω(m^(1+2/(k+1))/(r² log n)) space → graphs on Fin n; explicit Δ and a,b,κ > 0 before ∀N ∃n≥N ∃G, followed by every r and oracle; division-free natural-log inequality; reason: finite relabeling changes no instance, logarithm bases are absorbed in κ, and multiplication is equivalent for n>1; arbitrarily large thresholds remove small-n division issues
--   - encoding: weighted undirected storage graph, zero diagonal, absent edges infinite → SimpleGraph storage with symmetric ℝ≥0∞ weights and the same zero/infinity extension; reason: loops contribute zero and are never needed; removing any counted loop can only strengthen the space lower bound
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Theorem 1, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Conjecture
import Definitions.Def_PivotADO_OneHop_Oracle

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- Theorem 1, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.17.
All constants precede n and G; the same graph works for every r, including r > n.
The open constant-degree girth conjecture is an explicit hypothesis. -/
theorem theorem_1 (hconj : ConstantDegreeGirthConjecture) :
    ∀ k : ℝ, 1 ≤ k → ∃ (Δ : ℕ) (a b κ : ℝ),
      0 < a ∧ 0 < b ∧ 0 < κ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N ≤ n ∧ (∀ v, G.degree v ≤ Δ) ∧
        a * (n : ℝ) ≤ (edgeCount G : ℝ) ∧ (edgeCount G : ℝ) ≤ b * (n : ℝ) ∧
        ∀ r : ℕ, 1 ≤ r → ∀ O : Oracle G r k,
          κ * (edgeCount G : ℝ) ^ (1 + 2 / (k + 1)) ≤
            (r : ℝ) ^ 2 * Real.log (n : ℝ) * (edgeCount O.storage.graph : ℝ) := by sorry

end PivotADO.OneHop
