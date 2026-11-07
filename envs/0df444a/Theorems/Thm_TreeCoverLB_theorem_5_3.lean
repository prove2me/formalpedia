-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_5_3
-- name    : TreeCoverLB.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:36.784887+00:00
-- url     : https://prove2.me/theorems/fbd53dc1-a463-407e-84e7-0fa0eb5fc6b4
-- title:
--   Theorem 5.3 (Füredi–Gyárfás): an intersecting $r$-partite hypergraph has $\nu^*\le r-1$
-- statement:
--   Let $r\ge 2$. If $H$ is an intersecting $r$-partite $r$-uniform hypergraph, then
--   $$
--   \nu^*(H)\le r-1,
--   $$
--   i.e. every fractional matching of $H$ has value at most $r-1$.
--
--   With $r=k$ this gives Corollary 5.4: every point of $|I_{p,k}|$ has a marginal atom of mass at least $1/(k-1)$.
--
--   Differences from the source:
--   - encoding: an intersecting r-partite r-uniform hypergraph and ν*(H) ≤ r − 1 → a finite set of words over r vertex classes, pairwise agreeing; every fractional matching has value ≤ r − 1; reason: edges are words; repeated edges do not change ν*; the maximum is attained
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 5.3, p.19 (PDF p.21); cited from [FG91, Theorem 2]

import Mathlib
import Definitions.Def_TreeCoverLB_IsFracMatching

open Classical

namespace TreeCoverLB

/-- **Theorem 5.3** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Theorem 5.3, p.19 (PDF p.21); cited from [FG91, Theorem 2]): let
`r ≥ 2`. If `H` is an intersecting `r`-partite `r`-uniform hypergraph, then `ν*(H) ≤ r − 1`: every
fractional matching of `H` has value at most `r − 1`.

**Formalization Note** The vertex classes are arbitrary types `α 0, …, α (r−1)`, an edge is a word
picking one vertex from each class, and `H` is a finite set `S` of words (repeated edges do not change
`ν*`). -/
theorem theorem_5_3 (r : ℕ) (hr : 2 ≤ r) {α : Fin r → Type*} (S : Finset ((i : Fin r) → α i))
    (hS : IsIntersecting S) (f : ((i : Fin r) → α i) → ℝ) (hf : IsFracMatching S f) :
    ∑ x ∈ S, f x ≤ (r : ℝ) - 1 := by sorry

end TreeCoverLB
