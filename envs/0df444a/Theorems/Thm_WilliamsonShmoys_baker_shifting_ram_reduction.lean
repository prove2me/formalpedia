-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_shifting_ram_reduction
-- name    : WilliamsonShmoys.baker_shifting_ram_reduction
-- status  : Open
-- author  : @amirh
-- created : 2026-10-30T23:33:34.94026+00:00
-- url     : https://prove2.me/theorems/9cfb4667-2638-4d30-91f4-fc0d1744d0ea
-- title:
--   RAM reduction: an exact bounded-tree-width independent-set program yields the best-of-$k$ shifted band solver
-- statement:
--   Baker's shifting step, stated as a reduction between programs for the unit-cost real RAM of `WilliamsonShmoys_PlanarIndependentSetRAM`.
--
--   For an adjacency table $E$ on $\{0,\dots,n-1\}$ let $G$ be its graph (distinct $u,v$ adjacent if and only if $E(u,v)=1$ or $E(v,u)=1$), let $\ell(v)$ be the BFS level of $v$ (`bakerLevel`: the distance from the smallest vertex of its connected component), and write $\omega(X)=\sum_{v\in X}\omega(v)$ for a real weight vector $\omega$. The standard input layout with parameter $p$ puts $n,p$ in natural cells $0,1$, the table in the next $n^2$ natural cells, $\omega$ in real cells $0,\dots,n-1$, and $0$ everywhere else; the output bitmap is natural cells $2+n^2,\dots,1+n^2+n$.
--
--   Suppose $P$ is a program and $C_0,d_0>0$ are constants such that $P$ solves maximum-weight independent set exactly on graphs of tree-width at most $w$: for every $w,n$, every table $E$ whose graph $G$ has tree-width at most $w$ and every $\omega$, the program $P$ started on the standard input layout with parameter $w$ reaches a `halt` instruction after $t$ operations with $t+1\le C_0\,2^{d_0w}(n+1)^2$, its output bitmap consists of $0/1$ cells, and it describes an independent set $A$ of $G$ with $\omega(S)\le\omega(A)$ for every independent set $S$ of $G$.
--
--   Then there are a program $Q$ and constants $C,d>0$ such that for every $k\ge1$, every $n$, every table $E$ and every $\omega$ the following holds. If for each $0\le j<k$ the graph $G_j$ obtained from $G$ by deleting the vertices $v$ with $\ell(v)\equiv j\pmod k$ has tree-width at most $3k$, then $Q$, started on the standard input layout with parameter $k$, reaches a `halt` instruction after $t$ operations with
--
--   $$t+1\le C\,2^{dk}\,(n+1)^2,$$
--
--   its output bitmap consists of $0/1$ cells and describes an independent set $A$ of $G$, and
--
--   $$\omega(S)\le\omega(A)\qquad\text{for all } j<k \text{ and all independent sets } S \text{ of } G \text{ with } \ell(v)\not\equiv j \pmod k \text{ for every } v\in S.$$
--
--   This isolates the shifting part of the algorithmic half of Baker's PTAS (Williamson–Shmoys, Section 10.2, proof of Theorem 10.11): compute the BFS levels, solve maximum-weight independent set exactly on each of the $k$ graphs $G_j$, and return the heaviest of the $k$ solutions. Combined with an exact bounded-tree-width solver such as `WilliamsonShmoys.treewidth_mwis_ram_solver`, it gives `WilliamsonShmoys.band_treewidth_ram_solver`.
--
--   **Formalization Note** The hypothesis on $P$ is the body of `WilliamsonShmoys.treewidth_mwis_ram_solver` with its existentially quantified program and constants turned into parameters, and the conclusion is verbatim the statement of `WilliamsonShmoys.band_treewidth_ram_solver`. The hypothesis constrains only the input-output behaviour and running time of $P$, not which memory cells it uses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272, https://doi.org/10.1017/CBO9780511921735: compute the BFS levels, for each of the k shifts solve the tree-width-bounded instance exactly, and output the best of the k solutions. Shifting technique: B. S. Baker, Approximation algorithms for NP-complete problems on planar graphs, J. ACM 41(1) (1994) 153-180, https://doi.org/10.1145/174644.174650.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false
open scoped BigOperators

namespace WilliamsonShmoys
theorem baker_shifting_ram_reduction
    (solver : List PlanarRAMInstruction) (C₀ d₀ : ℕ) (hC₀ : 0 < C₀) (hd₀ : 0 < d₀)
    (hsolver : ∀ (w n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
      let G := SimpleGraph.fromRel (fun u v => edge u v = true)
      RobertsonSeymour1986.GM5.TreewidthLE G w →
      ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * w) * (n + 1) ^ 2 ∧
        let result := planarRAMRun solver (planarRAMInput n w edge weight) t
        solver[result.pc]? = some PlanarRAMInstruction.halt ∧
        (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
        G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
        ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
          ∑ i ∈ S, weight i ≤ ∑ i ∈ planarRAMOutput n result, weight i) :
    ∃ (program : List PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        (∀ j < k, RobertsonSeymour1986.GM5.TreewidthLE
          (G.induce {v : Fin n | bakerLevel G v % k ≠ j}) (3 * k)) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := planarRAMRun program (planarRAMInput n k edge weight) t
          program[result.pc]? = some PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
          ∀ j < k, ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
            (∀ v ∈ S, bakerLevel G v % k ≠ j) →
            ∑ i ∈ S, weight i ≤ ∑ i ∈ planarRAMOutput n result, weight i := by sorry
end WilliamsonShmoys
