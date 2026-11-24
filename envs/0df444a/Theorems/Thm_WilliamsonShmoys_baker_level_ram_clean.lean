-- Prove2me | Theorems.Thm_WilliamsonShmoys_baker_level_ram_clean
-- name    : WilliamsonShmoys.baker_level_ram_clean
-- status  : Open
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:39:22.859141+00:00
-- url     : https://prove2.me/theorems/90de9d95-4985-4013-b208-12e64d40515b
-- title:
--   Baker BFS level classes mod $k$ as a clean $O(n^2)$ RAM subroutine
-- statement:
--   **Baker's breadth-first search as a clean RAM subroutine.** In the unit-cost real RAM of the mission (`WilliamsonShmoys_PlanarIndependentSetRAM`), one fixed program computes every vertex's Baker level class in $O(n^2)$ operations. It leaves the rest of memory exactly as it found it and falls through to the instruction after its last one.
--
--   Let $G$ be the simple graph of an adjacency table $E$ on $\{0,\dots,n-1\}$: distinct $u,v$ are adjacent iff $E(u,v)=1$ or $E(v,u)=1$. Let $L(v)$ be the Baker BFS level of $v$ (`bakerLevel`): the graph distance from the smallest label in the connected component of $v$ to $v$.
--
--   **Claim.** There are a finite program $A$ and a constant $C>0$ with the following property. For every $k\ge 1$, $n\ge 0$, table $E$ and real weights $\omega$, start $A$ on the standard input $(n,k,E,\omega)$. Then there is a step count $T$ with
--   $$T+1\le C\,(n+1)^2$$
--   such that the program counter stays inside $A$ (i.e. $<|A|$) at every step before $T$, and after exactly $T$ steps the state is the input state with
--   $$\text{natural cell } 2+n^2+n+v \;=\; L(v) \bmod k \qquad (0\le v<n),$$
--   every other natural and real cell equal to its input value, and program counter equal to $|A|$.
--
--   **Role.** This is the BFS phase of Baker's technique (Williamson–Shmoys, Section 10.2, p. 270), with the levels reduced mod $k$ because only the class $L(v) \bmod k$ is used to mask the graph. Because the final state is specified exactly and the program ends by falling through to position $|A|$, any program can be appended after $A$ (with its jump targets shifted by $|A|$). This is how it is used in the decomposition of `WilliamsonShmoys.baker_masked_runs_ram_core`.
--
--   **Formalization note.** The final state is `{ bakerLevelInput n k edge weight with pc := A.length }` (definition `WilliamsonShmoys_BakerLevelInput`). The RAM has no division, so the residue must be maintained incrementally, e.g. a child's class is its parent's class plus one, wrapped to $0$ at $k$. Any scratch cells used by the search must be reset to zero. Scanning possible roots in increasing label order makes each search start at the smallest label of its component, as `bakerRoot` requires.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, Section 10.2 (Baker's technique), proof of Theorem 10.11, author electronic manuscript pp. 270–272, in the mission's RAM model (WilliamsonShmoys_PlanarIndependentSetRAM).

import Definitions.Def_WilliamsonShmoys_BakerLevelInput

set_option autoImplicit false

theorem WilliamsonShmoys.baker_level_ram_clean :
    ∃ (A : List WilliamsonShmoys.PlanarRAMInstruction) (C : ℕ), 0 < C ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        ∃ T : ℕ, T + 1 ≤ C * (n + 1) ^ 2 ∧
          (∀ t < T, (WilliamsonShmoys.planarRAMRun A
            (WilliamsonShmoys.planarRAMInput n k edge weight) t).pc < A.length) ∧
          WilliamsonShmoys.planarRAMRun A (WilliamsonShmoys.planarRAMInput n k edge weight) T =
            { WilliamsonShmoys.bakerLevelInput n k edge weight with pc := A.length } := by sorry
