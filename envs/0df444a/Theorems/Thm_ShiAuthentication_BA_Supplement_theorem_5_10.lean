-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_theorem_5_10
-- name    : ShiAuthentication.BA.Supplement.theorem_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:27:23.17342+00:00
-- url     : https://prove2.me/theorems/b4d9d7b5-ab64-4934-abbf-0db68df9103c
-- title:
--   Theorem 5.10 — maximum resilience: $A_{BB}(n,n-1)=\binom n2-1$
-- statement:
--   Let $n\ge3$ and let $S$ be a designated sender. Then
--   $$A_{BB}(n,n-1)=\binom{n}{2}-1,$$
--   the minimum number of authentication edges of a public authentication graph $G$ on which broadcast from $S$ tolerating $n-1$ faults is possible. An optimal setup is obtained from any ordering $S=v_0,v_1,\dots,v_{n-1}$ of the parties starting at $S$: take all forward edges $v_i\to v_j$ ($i<j$) except $v_{n-2}\to v_{n-1}$ (Figure 2). For every such ordering this graph supports $\mathrm{BB}(G,S,n-1)$ and has exactly $\binom n2-1$ edges.
--
--   The theorem gives the exact authentication cost of broadcast at maximum resilience: a complete PKI is not needed, but only one edge can be saved.
--
--   Differences from the source:
--   - encoding: values of A_T(n, t) in ℕ ∪ {+∞} → ℕ∞, compared with real bounds after the cast ℕ∞ → ℝ≥0∞ and ENNReal.ofReal; reason: +∞ is the infimum of the empty family (Definition 3.3); an upper bound in ℝ≥0∞ also asserts finiteness
--   - encoding: BB(G, S, t) feasible → BBPossible .publicGraph t G S; reason: Definition 3.1 in the model of §3.1, where the authentication graph G is public
--   - reading: An optimal setup consists of all forward edges in an order S = v₀, …, v_{n−1} except v_{n−2} → v_{n−1} → for every ordering v with v₀ = S, the forward graph supports BB(G, S, n − 1) and has C(n, 2) − 1 edges; reason: the construction of §5.4.1 works for an arbitrary order starting at S; optimal means feasible with the minimum number of edges
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Theorem 5.10 and Figure 2, p. 34 (Figure 2 on p. 14); proof pp. 34–35

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Theorem 5.10 (Maximum resilience)**, p. 34. For `n ≥ 3` and a designated sender `S`,
`A_BB(n, n − 1) = C(n, 2) − 1`. An optimal setup consists of all forward edges in an order
`S = v₀, v₁, …, v_{n−1}` except `v_{n−2} → v_{n−1}` (Figure 2): for **every** such order this graph
supports `BB(G, S, n − 1)` and has exactly `C(n, 2) − 1` edges. -/
theorem theorem_5_10 (n : ℕ) (hn : 3 ≤ n) (S : Fin n) :
    ABB (n - 1) S = ((n.choose 2 - 1 : ℕ) : ℕ∞) ∧
    ∀ v : Fin n ≃ Fin n, (v.symm S).val = 0 →
      BBPossible .publicGraph (n - 1) (forwardGraph v) S ∧
      edgeCount (forwardGraph v) = n.choose 2 - 1 := by sorry

end ShiAuthentication.BA.Supplement
