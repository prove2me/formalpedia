-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_theorem_1
-- name    : SpreadMatchCircuit.Matching.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:29.205303+00:00
-- url     : https://prove2.me/theorems/dd1f7a72-aea8-4760-b7a8-41bb9da1f6db
-- title:
--   Theorem 1 — monotone circuits distinguishing $k$-matchings from no $q$-matching need $\exp(\Omega(q/\sqrt k))$ gates
-- statement:
--   There are absolute constants $a,c>0$ such that the following holds. Let $q<k$ be natural numbers with $k\le n/2$, and let $(L,L^{\mathrm c})$ be a partition of $[n]$ with $|L|\ge k$ and $|L^{\mathrm c}|\ge k$. If a monotone Boolean circuit $C$ on the edge variables of $[n]$ outputs $1$ on every graph bipartite with these sides that has a matching of size $k$, and outputs $0$ on every such graph that has no matching of size $q$, then
--
--   $$\mathrm{size}(C)\ \ge\ a\,\exp\!\Big(\frac{c\,q}{\sqrt k}\Big).$$
--
--   In particular, every monotone circuit that distinguishes $n$-vertex bipartite graphs with matchings of size $k$ from graphs with no matchings of size $q$ has $\exp(\Omega(q/\sqrt k))$ gates, for the full range $q<k\le n/2$. Taking $k=n/2$ and $q=n/4$ gives the bound $\exp(\Omega(\sqrt n))$ for separating perfect matchings from graphs with no matching of size $n/4$.
--
--   **Formalization Note** The constants $a,c$ are absolute: they precede $n,k,q,L$ and $C$. The prefactor $a$ makes the statement meaningful for every parameter, including bounded $q/\sqrt k$, where it reduces to $\mathrm{size}(C)\ge 1$. No parity of $n$ and no balance of the sides is assumed. The promise is strict: "no matching of size $q$" means matching number below $q$. A $q$-vertex cover can contain a $q$-matching (for $n=8$, $k=4$, $q=2$, sides $\{1,2,3,4\},\{5,6,7,8\}$, $W_0=\{1,2\}$, the cross edges of $G(W_0)$ contain $\{\{1,5\},\{2,6\}\}$), so its cross-edge part is a guaranteed negative promised graph when the cover size is $q-1$, rather than $q$. The source's full incident graph need not be bipartite; for the fixed-partition promise its gates can be composed with deletion of non-cross edges. This affects only a constant in the exponent, as $q-1\ge q/2$ for $q\ge 2$.
--
--   Differences from the source:
--   - generalization: C correct on all n-vertex bipartite graphs → C correct only on the graphs bipartite with fixed sides L and its complement, for any L with both sides of size at least k; reason: a circuit correct on all bipartite graphs is correct for L, and such L exists because k ≤ n/2, so the source's statement is the case of any one such L.
--   - encoding: exp(Ω(q/√k)) gates → a·exp(c·q/√k) ≤ size with absolute constants a, c > 0 chosen before all parameters; reason: this is the asymptotic statement at every parameter value, with the prefactor covering bounded ratios.
--   - encoding: gates → all nodes, input nodes included; reason: the source calls input nodes input gates (p. 11), and the convention counting only binary gates differs by a constant factor after removing nodes that do not reach the output.
--   - encoding: q < k with q unrestricted below → natural q including q = 0; reason: with q = 0 the rejecting promise is empty and the bound reads size ≥ a, which holds for a ≤ 1.
--   - encoding: graphs on n vertices → finite sets of non-loop edges on Fin n, with an input variable for each edge; reason: these correspond exactly to simple graphs on n labelled vertices.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 2, Theorem 1 (proof pp. 10–13)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Promise

namespace SpreadMatchCircuit.Matching

/-- Theorem 1, p. 2: for `q < k ≤ n/2`, a monotone circuit distinguishing `n`-vertex bipartite
graphs with a `k`-matching from those with no `q`-matching has `exp(Ω(q/√k))` gates, with absolute
constants `a, c`. Correctness is required only on one bipartition `(L, Lᶜ)` with both sides of size
at least `k`. -/
theorem theorem_1 :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ (n k q : ℕ), q < k → 2 * k ≤ n →
        ∀ L : Finset (Fin n), k ≤ L.card → k ≤ Lᶜ.card →
          ∀ C : MonotoneCircuit (Edge n), DistinguishesMatchings C L k q →
            a * Real.exp (c * (q : ℝ) / Real.sqrt (k : ℝ)) ≤ (C.size : ℝ) := by sorry

end SpreadMatchCircuit.Matching
