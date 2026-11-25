-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_union_output_bound
-- name    : WilliamsonShmoys.baker_union_output_bound
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T10:16:39.860684+00:00
-- url     : https://prove2.me/theorems/924a784b-2e19-4c77-b744-81bb2e2dd475
-- title:
--   Best copy of an optimal independent set of the union of masked graphs
-- statement:
--   This is the combinatorial core of extracting Baker's answer from one solver call on the disjoint union of the $k$ masked graphs.
--
--   Let $G$ be a graph on $\{0,\dots,n-1\}$ with levels $\ell(v)$, and let $k\ge1$. Let $U$ be the graph on $\{0,\dots,k-1\}\times\{0,\dots,n-1\}$ in which $(c,v)\sim(c,w)$ iff $vw\in E(G)$ and $\ell(v)\bmod k\ne c\ne\ell(w)\bmod k$. Give $(c,v)$ the weight $w'(c,v)=w(v)$ if $\ell(v)\bmod k\ne c$ and $0$ otherwise. Let $A$ be a maximum-$w'$ independent set of $U$, and let $c^\*$ be a copy maximising $w'(A\cap(\{c\}\times V))$. Put
--
--   $$O=\{v:\ (c^\*,v)\in A,\ \ell(v)\bmod k\ne c^\*\}.$$
--
--   Then $O$ is independent in $G$. Moreover, for every $j<k$ and every independent set $S$ of the masked graph $G_j=G-\{v:\ell(v)\bmod k=j\}$,
--
--   $$\sum_{i\in S,\ \ell(i)\bmod k\ne j} w(i)\ \le\ \sum_{i\in O} w(i).$$
--
--   So the single call produces a solution at least as good as the best of the $k$ shifted solutions, as Baker's shifting argument requires.
--
--   **Formalization Note.** $G_j$ is written as `SimpleGraph.fromRel (fun u v => G.Adj u v ∧ lvl u % k ≠ j ∧ lvl v % k ≠ j)`. Sums over $S$ use the masked weight.
-- source:
--   Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (shifting technique)

import Mathlib

set_option autoImplicit false
open Classical

theorem WilliamsonShmoys.baker_union_output_bound {n : ℕ} (G : SimpleGraph (Fin n)) (lvl : Fin n → ℕ) (k : ℕ) (weight : Fin n → ℝ)
    (A : Finset (Fin k × Fin n))
    (hA : (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧
        lvl x.2 % k ≠ x.1.val ∧ lvl y.2 % k ≠ x.1.val)).IsIndepSet (A : Set (Fin k × Fin n)))
    (hopt : ∀ S : Finset (Fin k × Fin n),
      (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧
        lvl x.2 % k ≠ x.1.val ∧ lvl y.2 % k ≠ x.1.val)).IsIndepSet (S : Set (Fin k × Fin n)) →
      ∑ x ∈ S, (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0) ≤
        ∑ x ∈ A, (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0))
    (cs : Fin k)
    (hbest : ∀ c : Fin k, ∑ x ∈ A.filter (fun x => x.1 = c), (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0) ≤
      ∑ x ∈ A.filter (fun x => x.1 = cs), (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0)) :
    G.IsIndepSet ((Finset.univ.filter (fun v => (cs, v) ∈ A ∧ lvl v % k ≠ cs.val) : Finset (Fin n)) : Set (Fin n)) ∧
    ∀ j < k, ∀ S : Finset (Fin n),
      (SimpleGraph.fromRel (fun u v => G.Adj u v ∧ lvl u % k ≠ j ∧ lvl v % k ≠ j)).IsIndepSet (S : Set (Fin n)) →
      ∑ i ∈ S, (if lvl i % k ≠ j then weight i else 0) ≤
        ∑ i ∈ Finset.univ.filter (fun v => (cs, v) ∈ A ∧ lvl v % k ≠ cs.val), weight i := by sorry
