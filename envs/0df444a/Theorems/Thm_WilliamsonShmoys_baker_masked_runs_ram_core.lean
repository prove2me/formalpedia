-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_masked_runs_ram_core
-- name    : WilliamsonShmoys.baker_masked_runs_ram_core
-- status  : Open
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:21:36.155668+00:00
-- url     : https://prove2.me/theorems/e6669bf7-d1da-4da0-bcea-34da77e2de56
-- title:
--   Baker shifting in the RAM: run a black-box solver on all $k$ masked instances and keep the best filtered answer
-- statement:
--   **Running a black-box RAM solver on all $k$ Baker-masked instances and keeping the best filtered answer.** This is the purely computational half of Baker's shifting step (Williamson–Shmoys, Section 10.2, pp. 270–272), stated in the unit-cost real RAM of the mission (`WilliamsonShmoys_PlanarIndependentSetRAM`). It contains no graph theory beyond computing BFS levels: the solver is an arbitrary program, and only its halting times are assumed.
--
--   Fix a program $P$ (the *solver*) and constants $C_0, d_0 \in \mathbb N$. The claim is that there are one program $Q$ and constants $C, d > 0$ with the following property.
--
--   Let $k \ge 1$, $n \ge 0$, let $E : \{0,\dots,n-1\}^2 \to \{0,1\}$ be an adjacency table and $\omega : \{0,\dots,n-1\} \to \mathbb R$ a weight vector. Let $G$ be the simple graph in which distinct $u, v$ are adjacent iff $E(u,v)=1$ or $E(v,u)=1$, and let $L(v)$ be the Baker BFS level of $v$ (`bakerLevel`: the distance from $v$ to the smallest label in its connected component). For $j \in \mathbb N$ define the **$j$-th masked instance** $I_j$ as the standard input layout with parameter $3k$, table and weights
--   $$E_j(u,v) = E(u,v)\cdot[L(u) \not\equiv j]\cdot[L(v)\not\equiv j], \qquad \omega_j(i) = \begin{cases}\omega(i) & L(i)\not\equiv j \pmod k,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   **Hypothesis.** For every $j < k$, the solver started on $I_j$ reaches a `halt` instruction after some $t_j$ steps with $t_j + 1 \le C_0\, 2^{3 d_0 k} (n+1)^2$.
--
--   **Conclusion.** $Q$, started on the standard input $(n, k, E, \omega)$, reaches a `halt` instruction after some $t$ steps with
--   $$t + 1 \le C\, 2^{dk} (n+1)^2,$$
--   every output cell $2 + n^2 + i$ holds $0$ or $1$, and, writing $\mathrm{out}(Q)$ for the output bitmap and $\mathrm{out}_j$ for the solver's output bitmap on $I_j$ at any halting time:
--
--   1. there is $j_0 < k$ (and a halting time of the solver on $I_{j_0}$) with $\mathrm{out}(Q) = \{\, i \in \mathrm{out}_{j_0} : L(i) \not\equiv j_0 \pmod k \,\}$;
--   2. for every $j < k$ and every halting time of the solver on $I_j$,
--   $$\sum_{\substack{i \in \mathrm{out}_j\\ L(i)\not\equiv j}} \omega(i) \;\le\; \sum_{i \in \mathrm{out}(Q)} \omega(i).$$
--
--   **Intended construction.** Compute all BFS levels in $O(n^2)$ operations on the adjacency table (BFS from each unvisited vertex in increasing label order, so each search starts at the smallest label of its component). For each $j < k$, write $I_j$ into a region reserved for the solver and run a relocated copy of $P$: its jump targets are shifted by a constant, and every memory access to logical cell $a$ is redirected to physical cell $2a+1$ (odd cells for the solver, even cells for $Q$'s own data), with each written address logged so that all touched cells can be reset to zero before the next run. When the copy halts, filter its bitmap by $L(i)\not\equiv j$, compute the filtered weight with real additions, and keep the best bitmap so far by a real comparison. Each simulated solver step costs $O(1)$ operations, so the total is $O\big(k\,(C_0 2^{3d_0k} + 1)(n+1)^2\big) \le C\,2^{dk}(n+1)^2$ with, e.g., $d = 3d_0 + 1$.
--
--   Together with the solver's own correctness on bounded-tree-width graphs, this lemma gives the parent theorem `WilliamsonShmoys.baker_masked_best_of_runs_ram`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, Section 10.2 (Baker's technique), proof of Theorem 10.11, author electronic manuscript pp. 270–272. Computational half of the shifting step, in the mission's RAM model (WilliamsonShmoys_PlanarIndependentSetRAM).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.baker_masked_runs_ram_core
    (solver : List WilliamsonShmoys.PlanarRAMInstruction) (C₀ d₀ : ℕ) :
    ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        let maskedEdge : ℕ → Fin n → Fin n → Bool := fun j u v =>
          edge u v && decide (WilliamsonShmoys.bakerLevel G u % k ≠ j) &&
            decide (WilliamsonShmoys.bakerLevel G v % k ≠ j)
        let maskedWeight : ℕ → Fin n → ℝ := fun j i =>
          if WilliamsonShmoys.bakerLevel G i % k ≠ j then weight i else 0
        let inst : ℕ → WilliamsonShmoys.PlanarRAMState := fun j =>
          WilliamsonShmoys.planarRAMInput n (3 * k) (maskedEdge j) (maskedWeight j)
        (∀ j < k, ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * (3 * k)) * (n + 1) ^ 2 ∧
          solver[(WilliamsonShmoys.planarRAMRun solver (inst j) t).pc]? =
            some WilliamsonShmoys.PlanarRAMInstruction.halt) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := WilliamsonShmoys.planarRAMRun program
            (WilliamsonShmoys.planarRAMInput n k edge weight) t
          program[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          (∃ j₀ < k, ∃ t₀ : ℕ,
            solver[(WilliamsonShmoys.planarRAMRun solver (inst j₀) t₀).pc]? =
              some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
            WilliamsonShmoys.planarRAMOutput n result =
              (WilliamsonShmoys.planarRAMOutput n
                (WilliamsonShmoys.planarRAMRun solver (inst j₀) t₀)).filter
                  (fun i => WilliamsonShmoys.bakerLevel G i % k ≠ j₀)) ∧
          ∀ j < k, ∀ t' : ℕ,
            solver[(WilliamsonShmoys.planarRAMRun solver (inst j) t').pc]? =
              some WilliamsonShmoys.PlanarRAMInstruction.halt →
            ∑ i ∈ (WilliamsonShmoys.planarRAMOutput n
                (WilliamsonShmoys.planarRAMRun solver (inst j) t')).filter
                  (fun i => WilliamsonShmoys.bakerLevel G i % k ≠ j), weight i ≤
              ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i := by sorry
