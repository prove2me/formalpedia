-- Prove2me | Theorems.Thm_PivotADO_OneHop_Supplement_theorem_2
-- name    : PivotADO.OneHop.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:24.418542+00:00
-- url     : https://prove2.me/theorems/d325c3e2-aad3-484b-bec0-9349b07df427
-- title:
--   Theorem 2 — every $r$-pivot $\beta$-hop $k$-stretch ADO needs space $\tilde\Omega(m^{1+2/(\beta(k+1))})$, improved for $\beta=2$
-- statement:
--   Assume Conjecture 1 (the constant-degree Erdős girth conjecture). Fix a real $k\ge1$ and an integer $\beta\ge1$. Then there are constants $\Delta\in\mathbb N$ and $a,b,\kappa>0$ such that for every threshold $N$ there are $n\ge N$ and a simple graph $G$ on $n$ vertices with maximum degree at most $\Delta$ and $m=|E(G)|$ edges, $an\le m\le bn$, with the following property: for every integer $r\ge1$ and every $r$-pivot $\beta$-hop $k$-stretch ADO $(H,P)$ for $G$ (Definition 3),
--
--   $$\kappa\,m^{1+\frac{2}{\beta(k+1)}}\le r^2\,(\log n)^{6-4/\beta}\,|E_H|,$$
--
--   and, if $\beta=2$, moreover
--
--   $$\kappa\,m^{1+\frac{1}{k+1}}\le r^2\,(\log n)^{3}\,\log(r+1)\,|E_H|.$$
--
--   In words: on these constant-degree sparse graphs every such oracle requires $\Omega\bigl(m^{1+2/(\beta(k+1))}/(r^2\log^{6-4/\beta}n)\bigr)$ space, and for $\beta=2$ it requires $\Omega\bigl(m^{1+1/(k+1)}/(r^2\log^3 n\log(r+1))\bigr)$ space. The constants depend only on $k$ and $\beta$, and the graph does not depend on $r$ or on the oracle.
--
--   This extends the one-hop lower bound of the mission's goal (Theorem 1) to oracles that answer a query with up to $\beta$ stored hops through intermediate vertices. For $\beta=1$ the goal gives a stronger bound.
--
--   Differences from the source:
--   - encoding: constant-degree graphs with m = Θ(n) edges and an Ω(·) space bound, for arbitrarily large n → explicit Δ ∈ ℕ and a, b, κ > 0 chosen before the threshold N, then n ≥ N and G with maximum degree ≤ Δ, a·n ≤ m ≤ b·n, and the division-free inequality κ·m^e ≤ r²·(log n)^{6−4/β}·|E_H|; reason: this is the meaning of the asymptotic notation with constants depending on k and β only
--   - encoding: both conclusions for the same family of graphs → one conjunction with one κ; reason: a single κ (the smaller of the two) covers both bounds, so no instance changes
--   - encoding: log of unspecified base → natural logarithm Real.log, with the real exponent 6 − 4/β taken as a real power; reason: a change of base is absorbed in κ
--   - encoding: n-vertex graph with ℝ-valued distances and stored weights → SimpleGraph on Fin n, distances and stored weights in [0, ∞] (stored edges of weight ∞ allowed and counted); reason: Lean convention; no instance changes
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Theorem 2, p.20 (PDF p. 21); first stated p.3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Conjecture
import Definitions.Def_PivotADO_OneHop_Supplement_HopOracle

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop.Supplement

open PivotADO.OneHop

/-- Theorem 2, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.20 (PDF 21).
All constants precede `n` and `G`; the same graph works for every `r ≥ 1` and every
r-pivot β-hop k-stretch ADO. Both conclusions (the general bound and the improved bound
for `β = 2`) hold on the same graph. The open constant-degree girth conjecture is an
explicit hypothesis. -/
theorem theorem_2 (hconj : ConstantDegreeGirthConjecture) :
    ∀ k : ℝ, 1 ≤ k → ∀ β : ℕ, 1 ≤ β → ∃ (Δ : ℕ) (a b κ : ℝ),
      0 < a ∧ 0 < b ∧ 0 < κ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N ≤ n ∧ (∀ v, G.degree v ≤ Δ) ∧
        a * (n : ℝ) ≤ (edgeCount G : ℝ) ∧ (edgeCount G : ℝ) ≤ b * (n : ℝ) ∧
        ∀ r : ℕ, 1 ≤ r → ∀ O : HopOracle G r β k,
          κ * (edgeCount G : ℝ) ^ (1 + 2 / ((β : ℝ) * (k + 1))) ≤
              (r : ℝ) ^ 2 * Real.log (n : ℝ) ^ (6 - 4 / (β : ℝ)) *
                (edgeCount O.storage.graph : ℝ) ∧
          (β = 2 →
            κ * (edgeCount G : ℝ) ^ (1 + 1 / (k + 1)) ≤
              (r : ℝ) ^ 2 * Real.log (n : ℝ) ^ 3 * Real.log ((r : ℝ) + 1) *
                (edgeCount O.storage.graph : ℝ)) := by sorry

end PivotADO.OneHop.Supplement
