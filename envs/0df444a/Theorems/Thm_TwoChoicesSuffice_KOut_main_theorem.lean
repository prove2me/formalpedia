-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_main_theorem
-- name    : TwoChoicesSuffice.KOut.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:36.117434+00:00
-- url     : https://prove2.me/theorems/5f93f0b4-bea9-471b-889e-4c147cba1833
-- title:
--   Theorem 1 — $k$-out sampling leaves $O(n/k)$ intercomponent edges for every $k\ge2$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $G$ be any finite simple graph on $n$ vertices and $H^k_G$ its random with-replacement $k$-out subgraph, in which every vertex independently chooses $k$ incident edges uniformly with replacement. For every integer $k\ge2$,
--   $$
--   \mathbb E\bigl[x_G(H^k_G)\bigr]\le C\,\frac nk ,
--   $$
--   where $x_G(H)$ is the number of edges of $G$ joining distinct components of $H$. The constant does not depend on $n$, $G$ or $k$.
--
--   This resolves the conjecture of Holm, King, Thorup, Zamir and Zwick for all $k\ge2$. By the monotone coupling of §3 the same bound holds without replacement.
--
--   **Formalization Note** $O(n/k)$ is rendered as a single absolute constant quantified before the vertex type, the graph and $k$; Theorems 10 and 12 give the witness $C=1000$ ($6n/(k-2)\le18n/k$ for $k\ge3$, and $500n=1000\cdot n/2$). Graphs may be disconnected, irregular, empty or have isolated vertices; $k$ has no upper bound.
--
--   Differences from the source:
--   - encoding: E[x_G(H^k_G)] ≤ O(n/k) → ∃ C > 0, ∀ V G k ≥ 2, E[x_G(H^k_G)] ≤ C·n/k; reason: the standard reading of a uniform O-bound; C is chosen before every graph parameter
--   - encoding: G arbitrary; isolated vertices removed without loss (§3, PDF p. 7) → isolated vertices kept, each with a single dummy choice that yields no edge, and counted in n; reason: deleting isolates changes neither the law on the other vertices nor the crossing edges and only decreases n; the Lean convention is that reduction, with no extra hypothesis
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Theorem 1, printed p. 2, PDF p. 3; proof completed printed p. 24, PDF p. 25

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling

open scoped Classical

namespace TwoChoicesSuffice.KOut

universe u

/-- Theorem 1 (PDF p. 3, printed p. 2). There is an absolute constant `C > 0` such that for
every finite simple graph `G` on `n` vertices and every integer `k ≥ 2`, the random
with-replacement `k`-out subgraph `H^k_G` satisfies `E[x_G(H^k_G)] ≤ C · n / k`, i.e.
`E[x_G(H^k_G)] = O(n/k)` uniformly in `n`, `G` and `k`. -/
theorem main_theorem :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (k : ℕ), 2 ≤ k →
      kOutExpect G k (fun σ => (crossingCount G (prefixGraph G σ k) : ℝ)) ≤
        C * (Fintype.card V : ℝ) / (k : ℝ) := by sorry

end TwoChoicesSuffice.KOut
