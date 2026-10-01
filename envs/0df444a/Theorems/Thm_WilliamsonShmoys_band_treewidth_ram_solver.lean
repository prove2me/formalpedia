-- Prove2me | Theorems.Thm_WilliamsonShmoys_band_treewidth_ram_solver
-- name    : WilliamsonShmoys.band_treewidth_ram_solver
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-30T13:52:24.890332+00:00
-- url     : https://prove2.me/theorems/6203ea4c-4dc1-49b8-94fb-70379b4ed9a5
-- title:
--   RAM program: best of $k$ exact shifted optima for graphs whose BFS bands have tree-width $\\le 3k$
-- statement:
--   There is one finite program for the unit-cost real RAM of `WilliamsonShmoys_PlanarIndependentSetRAM` and constants $C,d>0$ with the following property. For every integer $k\ge1$, every $n$, every adjacency table on $\{0,\dots,n-1\}$ with graph $G$ and every real weight vector $w$, if for each $0\le j<k$ the graph obtained by deleting the vertices whose BFS level (`bakerLevel`) is $\equiv j \pmod k$ has tree-width at most $3k$, then the program, started on the standard input layout with accuracy parameter $k$, reaches a `halt` instruction after $t$ steps with
--
--   $$t+1 \le C\,2^{dk}(n+1)^2,$$
--
--   its output bitmap consists of $0/1$ cells and describes an independent set $A$ of $G$, and $A$ weighs at least as much as every independent set that avoids one residue class of levels:
--
--   $$\sum_{v\in S} w(v) \le \sum_{v\in A} w(v) \quad\text{for all } j<k \text{ and independent } S \text{ with } \ell(v)\not\equiv j \ (\mathrm{mod}\ k) \text{ for } v\in S.$$
--
--   This is the algorithmic half of Baker's PTAS (Williamson–Shmoys, Theorem 10.11): compute the BFS levels, and for each shift $j$ solve maximum-weight independent set exactly on the bounded-tree-width graph $G_j$ (find a tree decomposition of width $O(k)$, then dynamic programming), finally output the heaviest of the $k$ solutions. The hypothesis is purely combinatorial; planarity is not assumed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Algorithmic half: exact dynamic programming on tree decompositions for each of the k shifts, O(2^{O(k)} n^2) time overall.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false
open scoped BigOperators

namespace WilliamsonShmoys
theorem band_treewidth_ram_solver :
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
