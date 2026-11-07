-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_5_8
-- name    : TreeCoverLB.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:14.95068+00:00
-- url     : https://prove2.me/theorems/f3553cef-9252-4a79-8620-82eb71a5ad94
-- title:
--   Theorem 5.8 (Füredi): $\nu^*(H_S)=k-1$ forces an affine-plane configuration
-- statement:
--   Let $k\ge 3$, let $p\ge k-1$ be prime and $G=\mathbb Z_p$. Let $S\subseteq G^k$ be a pairwise agreeing family of words and $H_S$ the $k$-partite $k$-uniform hypergraph with edges $e_x=\{(1,x_1),\dots,(k,x_k)\}$, $x\in S$. If
--   $$
--   \nu^*(H_S)=k-1,
--   $$
--   then $S$ is an affine-plane configuration.
--
--   Differences from the source:
--   - encoding: ν*(H_S) = k − 1 → k − 1 is the greatest value of a fractional matching on the words of S; reason: definition of ν* as a maximum
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 5.8, p.21 (PDF p.23); cited from [Für89, Theorem 2.1]; standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsFracMatching
import Definitions.Def_TreeCoverLB_IsAffinePlaneConfig

open Classical

namespace TreeCoverLB

/-- **Theorem 5.8 (Füredi equality characterization)** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Theorem 5.8, p.21 (PDF p.23); cited from
[Für89, Theorem 2.1]; §5 standing assumptions p.18): let `k ≥ 3`, let `p ≥ k − 1` be prime and
`G = ℤ_p`. Let `S ⊆ G^k` be a pairwise agreeing family of words, and let `H_S` be the associated
`k`-partite `k`-uniform hypergraph with edges `e_x = {(1, x_1), …, (k, x_k)}` (`x ∈ S`). If
`ν*(H_S) = k − 1`, then `S` is an affine-plane configuration.

**Formalization Note** "Pairwise agreeing" is `S ∈ I_{p,k}`. `ν*(H_S) = k − 1` is stated as: `k − 1` is
the greatest value of a fractional matching on `H_S` (edges are the words of `S`). -/
theorem theorem_5_8 (k : ℕ) (hk : 3 ≤ k) (p : ℕ) [Fact p.Prime] (hp : k - 1 ≤ p)
    (S : Finset (Fin k → ZMod p)) (hS : S ∈ agreementComplex p k)
    (hν : IsGreatest {v : ℝ | ∃ f : (Fin k → ZMod p) → ℝ,
      IsFracMatching (α := fun _ => ZMod p) S f ∧ ∑ x ∈ S, f x = v} ((k : ℝ) - 1)) :
    IsAffinePlaneConfig S := by sorry

end TreeCoverLB
