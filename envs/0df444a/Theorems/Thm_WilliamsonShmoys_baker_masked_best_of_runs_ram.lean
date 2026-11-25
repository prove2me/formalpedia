-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_masked_best_of_runs_ram
-- name    : WilliamsonShmoys.baker_masked_best_of_runs_ram
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T05:55:34.94416+00:00
-- url     : https://prove2.me/theorems/9cd4f83f-a088-4d3b-8711-40843d784ff4
-- title:
--   RAM core of Baker's shifting: best of k masked solver runs
-- statement:
--   Let `solver` be a unit-cost RAM program (in the instruction set of the mission) that solves maximum weight independent set exactly. On every instance $(n,w,\text{edge},\text{weight})$ whose graph $G$ has tree-width at most $w$, it halts within $C_0 2^{d_0 w}(n+1)^2$ operations and writes an independent set of maximum weight as an output bitmap.
--
--   Then there is one RAM program and constants $C,d>0$ with the following property. For every $k\ge1$ and every instance $(n,k,\text{edge},\text{weight})$, write $L(v)$ for the Baker BFS level (`bakerLevel`) and, for $j<k$, write $G_j$ for the graph on all $n$ vertices that keeps exactly the edges of $G$ with both ends of level $\not\equiv j \pmod k$. Assume every $G_j$ has tree-width at most $3k$. Then the program halts within $C2^{dk}(n+1)^2$ operations, its output bitmap encodes an independent set $A$ of $G$, and for every $j<k$ and every independent set $S$ of $G_j$
--
--   $$\sum_{i\in S,\;L(i)\not\equiv j} w_i\;\le\;\sum_{i\in A} w_i.$$
--
--   This is the RAM core of Baker's shifting technique (Williamson–Shmoys, Section 10.2, pp. 270–271). For each $j<k$, compute the BFS levels, mask the instance (delete the level-$j$ edges and zero the level-$j$ weights), run `solver` with parameter $3k$, discard the level-$j$ vertices from its answer, and keep the best of the $k$ candidates. The $k$ solver runs cost $k\,C_0 2^{3d_0 k}(n+1)^2$ operations, and BFS, masking and copying cost $O(k(n+1)^2)$.
--
--   **Formalization Note.** The masked graph is `SimpleGraph.fromRel (fun u v => G.Adj u v ∧ L u % k ≠ j ∧ L v % k ≠ j)`. The weight on the left is the masked weight, which is $0$ on level-$j$ vertices.
-- source:
--   Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, pp. 270–271 (proof of Theorem 10.11)

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.baker_masked_best_of_runs_ram
    (solver : List WilliamsonShmoys.PlanarRAMInstruction) (C₀ d₀ : ℕ) (hC₀ : 0 < C₀) (hd₀ : 0 < d₀)
    (hsolver : ∀ (w n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
      let G := SimpleGraph.fromRel (fun u v => edge u v = true)
      RobertsonSeymour1986.GM5.TreewidthLE G w →
      ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * w) * (n + 1) ^ 2 ∧
        let result := WilliamsonShmoys.planarRAMRun solver (WilliamsonShmoys.planarRAMInput n w edge weight) t
        solver[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
        (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
        G.IsIndepSet (WilliamsonShmoys.planarRAMOutput n result : Set (Fin n)) ∧
        ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
          ∑ i ∈ S, weight i ≤ ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i) :
    ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        (∀ j < k, RobertsonSeymour1986.GM5.TreewidthLE
          (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
            WilliamsonShmoys.bakerLevel G u % k ≠ j ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j))
          (3 * k)) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := WilliamsonShmoys.planarRAMRun program (WilliamsonShmoys.planarRAMInput n k edge weight) t
          program[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (WilliamsonShmoys.planarRAMOutput n result : Set (Fin n)) ∧
          ∀ j < k, ∀ S : Finset (Fin n),
            (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
              WilliamsonShmoys.bakerLevel G u % k ≠ j ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j)).IsIndepSet
              (S : Set (Fin n)) →
            ∑ i ∈ S, (if WilliamsonShmoys.bakerLevel G i % k ≠ j then weight i else 0) ≤
              ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i := by sorry
