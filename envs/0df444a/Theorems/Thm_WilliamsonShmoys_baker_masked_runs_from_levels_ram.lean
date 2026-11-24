-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_masked_runs_from_levels_ram
-- name    : WilliamsonShmoys.baker_masked_runs_from_levels_ram
-- status  : Open
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:39:36.860324+00:00
-- url     : https://prove2.me/theorems/ca26ee29-ced8-47a9-9016-b43b7b092915
-- title:
--   Baker shifting in the RAM from precomputed level classes: best of $k$ masked solver runs
-- statement:
--   **Running a black-box RAM solver on all $k$ Baker-masked instances, given the level classes.** This is the same statement as `WilliamsonShmoys.baker_masked_runs_ram_core`, except that the program starts from the input augmented with the Baker level classes (`WilliamsonShmoys_BakerLevelInput`) instead of the plain input. The breadth-first search is therefore not part of this task.
--
--   Fix a solver program $P$ and constants $C_0,d_0\in\mathbb N$. For $k\ge1$, a table $E$ with graph $G$ and weights $\omega$, let $L$ be the Baker BFS level. The masked instance $I_j$ is the standard input with parameter $3k$, table $E_j(u,v)=E(u,v)\,[L(u)\not\equiv j]\,[L(v)\not\equiv j]$ and weights $\omega_j(i)=\omega(i)$ if $L(i)\not\equiv j \pmod k$, and $0$ otherwise.
--
--   **Claim.** There are a program $B$ and constants $C,d>0$ such that the following holds whenever the solver halts on every $I_j$ ($j<k$) within $C_0 2^{3d_0k}(n+1)^2$ steps. Started on the state whose natural cell $2+n^2+n+v$ holds $L(v)\bmod k$ (and which otherwise equals the standard input $(n,k,E,\omega)$), $B$ halts within $C2^{dk}(n+1)^2$ steps with a $0/1$ output bitmap $\mathrm{out}$, such that:
--
--   1. $\mathrm{out}=\{\,i\in\mathrm{out}_{j_0}: L(i)\not\equiv j_0\,\}$ for some $j_0<k$, where $\mathrm{out}_j$ is the solver's output bitmap on $I_j$ at a halting time;
--   2. for every $j<k$ and every halting time of the solver on $I_j$,
--   $$\sum_{i\in\mathrm{out}_j,\ L(i)\not\equiv j}\omega(i)\ \le\ \sum_{i\in\mathrm{out}}\omega(i).$$
--
--   **Role and difficulty.** This is the selection loop of Baker's technique (Williamson–Shmoys, Section 10.2, proof of Theorem 10.11, pp. 270–272). The solver's behaviour is only specified from the exact standard input state, in which every other cell is zero. So each run needs a memory region that is fresh and disjoint from the caller's data. One construction relocates the solver's code and redirects logical cell $a$ to physical cell $2a+1$ (two `natAdd`s per indirect access). It logs every written address, and zeroes the logged cells and the input region between runs. Each simulated step then costs $O(1)$ operations, so the total is $O(k(C_0 2^{3d_0k}+1)(n+1)^2)$.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, Section 10.2 (Baker's technique), proof of Theorem 10.11, author electronic manuscript pp. 270–272, in the mission's RAM model (WilliamsonShmoys_PlanarIndependentSetRAM).

import Definitions.Def_WilliamsonShmoys_BakerLevelInput

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.baker_masked_runs_from_levels_ram
    (solver : List WilliamsonShmoys.PlanarRAMInstruction) (C₀ d₀ : ℕ) :
    ∃ (B : List WilliamsonShmoys.PlanarRAMInstruction) (C d : ℕ),
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
          let result := WilliamsonShmoys.planarRAMRun B
            (WilliamsonShmoys.bakerLevelInput n k edge weight) t
          B[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
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
