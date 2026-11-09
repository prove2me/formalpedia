-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_theorem_10
-- name    : TwoChoicesSuffice.KOut.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:10.192931+00:00
-- url     : https://prove2.me/theorems/9cb06219-5b9d-490a-baec-442b01ede522
-- title:
--   Theorem 10 — $\mathbb E[x_G(H^k_G)]\le 6n/(k-2)$ for every $k\ge3$
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices and $H^k_G$ its random $k$-out subgraph with replacement. For every integer $k\ge3$,
--   $$
--   \mathbb E\bigl[x_G(H^k_G)\bigr]\le\frac{6n}{k-2}=O(n/k).
--   $$
--
--   This settles the bound for all $k\ge3$ with an explicit constant.
--
--   **Formalization Note** The division is real division by $k-2>0$. The $O(n/k)$ remark of the source is the consequence $6n/(k-2)\le18n/k$ for $k\ge3$ and is not part of the formal conclusion.
--
--   Differences from the source:
--   - encoding: G arbitrary; isolated vertices removed without loss (§3, PDF p. 7) → isolated vertices kept, each with a single dummy choice that yields no edge, and counted in n; reason: deleting isolates changes neither the law on the other vertices nor the crossing edges and only decreases n; the Lean convention is that reduction, with no extra hypothesis
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Theorem 10, printed p. 12, PDF p. 13

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Theorem 10 (PDF p. 13, printed p. 12). Let `G` be a simple graph on `n` vertices. For
every integer `k ≥ 3`, the random with-replacement `k`-out subgraph `H^k_G` satisfies
`E[x_G(H^k_G)] ≤ 6n / (k - 2)`. -/
theorem theorem_10 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 3 ≤ k) :
    kOutExpect G k (fun σ => (crossingCount G (prefixGraph G σ k) : ℝ)) ≤
      6 * (Fintype.card V : ℝ) / ((k : ℝ) - 2) := by sorry

end TwoChoicesSuffice.KOut
