-- Prove2me | Theorems.Thm_VanderbeiLP_Networks_konig_theorem
-- name    : VanderbeiLP.Networks.konig_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T19:03:16.836681+00:00
-- url     : https://prove2.me/theorems/3facd2fa-c2ea-49dc-afbf-99aa90bf016b
-- title:
--   Theorem 14.3 — König's Theorem
-- statement:
--   Suppose there are $n$ girls and $n$ boys, that every girl knows exactly $k$ boys, and that every boy knows exactly $k$ girls, where "knowing" is symmetric: girl $i$ and boy $j$ either know each other or do not. Write $i\sim j$ when they do. If $k\ge 1$, then $n$ marriages can be arranged with everybody knowing his or her spouse: there is a bijection $\sigma$ from girls to boys with
--   $$i\sim\sigma(i)\qquad\text{for every girl }i.$$
--
--   In graph language: every $k$-regular bipartite graph with $k\ge1$ has a perfect matching. Vanderbei derives it as a combinatorial application of the Integrality Theorem 14.2.
--
--   **Formalization Note** Girls and boys are both indexed by `Fin n`, and the symmetric relation is a single relation `knows i j` between girl $i$ and boy $j$. The hypothesis $k\ge1$ is implicit in the book: its proof puts flow $1/k$ on each arc, and for $k=0<n$ the conclusion is false. The network in the proof need not be connected; the statement carries no connectedness hypothesis.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 216 (PDF 227), Theorem 14.3 and the clarifying paragraph after it

import Mathlib

namespace VanderbeiLP.Networks

/-- **Theorem 14.3, König's Theorem** (Vanderbei, *Linear Programming*, 4th ed., p. 216).
Suppose there are `n` girls and `n` boys, every girl knows exactly `k` boys and every boy knows
exactly `k` girls, "knowing" being symmetric (`knows i j`: girl `i` and boy `j` know each other).
Then `n` marriages can be arranged with everybody knowing his or her spouse: there is a
bijection `σ` from girls to boys with girl `i` knowing boy `σ i`. The hypothesis `0 < k` is
implicit in the book (its proof puts flow `1/k` on each arc; with `k = 0 < n` the claim fails). -/
theorem konig_theorem (n k : ℕ) (hk : 0 < k) (knows : Fin n → Fin n → Prop)
    [DecidableRel knows]
    (hgirl : ∀ i : Fin n, (Finset.univ.filter (fun j => knows i j)).card = k)
    (hboy : ∀ j : Fin n, (Finset.univ.filter (fun i => knows i j)).card = k) :
    ∃ σ : Fin n ≃ Fin n, ∀ i : Fin n, knows i (σ i) := by sorry

end VanderbeiLP.Networks
