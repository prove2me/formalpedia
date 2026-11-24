-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_union_single_call_ram
-- name    : WilliamsonShmoys.baker_union_single_call_ram
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T11:22:14.767487+00:00
-- url     : https://prove2.me/theorems/b22e577d-d5b9-439f-9a5e-32cae62765b9
-- title:
--   Single-call RAM core of Baker's shifting technique
-- statement:
--   This is the single-call version of the RAM core of Baker's shifting technique.
--
--   Let `solver` be a unit-cost RAM program that solves maximum weight independent set exactly on every instance whose graph has tree-width at most its parameter $w$, within $C_0 2^{d_0 w}(n+1)^2$ operations, as in `baker_masked_best_of_runs_ram`.
--
--   Then there is one RAM program and constants $C,d>0$ with the following property. For every $k\ge1$ and every instance $(n,k,\text{edge},\text{weight})$ with graph $G$ and Baker levels $L$, let $U$ be the disjoint union of the $k$ masked graphs. Its vertex set is $\{0,\dots,k-1\}\times V(G)$, and $(j,a)$ is adjacent to $(j,b)$ when $ab\in E(G)$ and $L(a),L(b)\not\equiv j \pmod k$. Assume $\operatorname{tw}(U)\le 3k$. Then the program halts within $C2^{dk}(n+1)^2$ operations, outputs an independent set $A$ of $G$, and for every $j<k$ and every independent set $S$ of the $j$-th masked graph,
--
--   $$\sum_{i\in S,\;L(i)\not\equiv j} w_i\;\le\;\sum_{i\in A} w_i.$$
--
--   The intended implementation builds the single instance $U$ on $kn$ vertices, with level-$j$ weights set to $0$ in copy $j$, and runs `solver` once from a clean memory. Because $U$ is a disjoint union, the optimal set it returns is optimal in every copy, so the best copy can be read off. One call suffices: the solver specification only covers runs from a fresh input layout, so a second call could not start from clean memory.
--
--   **Formalization Note.** $U$ is `SimpleGraph.fromRel` on `Fin k × Fin n` with relation $x.1=y.1\wedge G.\mathrm{Adj}\,x.2\,y.2\wedge L(x.2)\bmod k\ne x.1\wedge L(y.2)\bmod k\ne x.1$.
-- source:
--   Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, pp. 270–271 (proof of Theorem 10.11)

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.baker_union_single_call_ram
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
        RobertsonSeymour1986.GM5.TreewidthLE
          (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧
            G.Adj x.2 y.2 ∧ WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val ∧
              WilliamsonShmoys.bakerLevel G y.2 % k ≠ x.1.val))
          (3 * k) →
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
