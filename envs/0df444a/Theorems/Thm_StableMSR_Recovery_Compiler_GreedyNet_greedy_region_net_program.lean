-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_GreedyNet_greedy_region_net_program
-- name    : StableMSR.Recovery.Compiler.GreedyNet.greedy_region_net_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-18T14:43:03.263512+00:00
-- url     : https://prove2.me/theorems/358addcf-2ef5-41e9-a43b-b1c7288ec0df
-- title:
--   Executed greedy construction of a maximal separated region net
-- statement:
--   For any symmetric zero-diagonal distance array on $n$ points, nonnegative threshold $R$, and an input bitmap for a region $W$, a fixed deterministic program of 39 instructions writes a bitmap for a set $N$ satisfying
--   $$N\subseteq W,\qquad d(u,v)>R\text{ for distinct }u,v\in N,\qquad \forall x\in W\ \exists v\in N:\ d(x,v)\le R.$$
--   The set is inclusion-maximal among strictly $R$-separated subsets of $W$. The output buffer is disjoint from the input bitmap and may initially contain arbitrary values. The charged execution takes exactly $11n^2+14n+12$ steps and makes exactly $n^2$ distance queries. It preserves the input bitmap, integer memory outside the output buffer, real memory, tape position and the registers specified in the formal statement.
--
--   Taking the separation threshold to be twice the guessed clustering radius gives the greedy region net used in Appendices A.3 and A.4.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Section 4.3 and Appendices A.3 and A.4, greedy choice of a maximal strictly separated region net. https://arxiv.org/html/2611.03547v1. Supporting implementation theorem for mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.GreedyNet.greedy_region_net_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 39 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (R : ℝ) (b c : ℤ)
      (W : Finset (Fin n)) (s : Store),
      (∀ u v, d u v = d v u) → (∀ u, d u u = 0) → 0 ≤ R →
      s.ptrs 6 = (n:ℤ) → s.ptrs 103 = b → s.ptrs 108 = c → s.regs 109 = R →
      Bitmap s.imem c W → Separate (n := n) c b →
      ∀ (ω : ℕ → ℝ) (work : ℕ), ∃ N : Finset (Fin n),
      let result := (MinSumFPT.step P d ω)^[n*(11*n+14)+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(n*(11*n+14)+12) ∧
      Bitmap result.imem b N ∧ Bitmap result.imem c W ∧ N ⊆ W ∧
      (∀ u ∈ N, ∀ v ∈ N, u ≠ v → R < d u v) ∧
      (∀ u ∈ W, ∃ v ∈ N, d u v ≤ R) ∧
      (∀ T : Finset (Fin n), N ⊆ T → T ⊆ W →
        (∀ u ∈ T, ∀ v ∈ T, u ≠ v → R < d u v) → T = N) ∧
      (∀ x : ℤ, (x < b ∨ b+(n:ℤ) ≤ x) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, j ∉ ([100,101,102,104,105,106,107,112,113]:List ℕ) → result.cfg.ptrs j = s.ptrs j) ∧
      (∀ j : ℕ, j ≠ 110 → j ≠ 111 → result.cfg.regs j = s.regs j) ∧
      result.cfg.mem = s.mem ∧ result.queries = s.queries+n^2 ∧ result.tapePos = s.tapePos := by sorry
