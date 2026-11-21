-- Prove2me | Theorems.Thm_VWZClique_IntegerRAM_NativeArena_wordRam_of_projected_kernel
-- name    : VWZClique.IntegerRAM.NativeArena.wordRam_of_projected_kernel
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T13:38:17.655596+00:00
-- url     : https://prove2.me/theorems/4974777b-6c3b-4ef1-8899-379493da1fc4
-- title:
--   From a projected contraction on the word RAM to faster clique counting
-- statement:
--   Let $\omega_{\mathbb C}$ be the arithmetic exponent of complex matrix multiplication, and let $\epsilon_{36}$ be the exponent saving for the formalized recursion on nine-vertex patterns with at most $36$ edges. Suppose that the projected contraction has a fixed word-RAM implementation with polynomial workspace, that it returns the exact trace and preserves the suspended recursion frames, and that its runtime satisfies the per-frame bound in `ProjectionKernel`. If its square multiplication cost obeys $\operatorname{mm}(n)\le Cn^{\omega_{\mathbb C}+\epsilon_{36}/8}$ for every $n\ge1$, then there are constants $\delta>0$ and $K_0$ such that for each $k\ge K_0$, the number of $k$-cliques in an $n$-vertex graph can be computed on the logarithmic-word RAM in $O(n^{(\omega_{\mathbb C}-\delta)k/3})$ time.
-- source:
--   V. Vassilevska Williams and O. Zamir, “The k-Clique hypothesis is dead, for good,” Theorem 1.1 and Appendix A (word-RAM implementation). https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_VWZClique_NativeProjectionContract
open OAI.MatrixMultiplication.Arithmetic VWZClique VWZClique.UniformFolds VWZClique.IntegerRAM.NativeArena

theorem VWZClique.IntegerRAM.NativeArena.wordRam_of_projected_kernel
    {mm : ℕ → ℕ} {T : ℕ} (pk : VWZClique.IntegerRAM.NativeArena.ProjectionKernel mm T)
    {C : ℝ} (hC : 0 < C)
    (rate : ∀ n : ℕ, 1 ≤ n → (mm n : ℝ) ≤ C * (n : ℝ) ^
      (OAI.MatrixMultiplication.Arithmetic.omega ℂ + (VWZClique.UniformFolds.levelSaving 36).val / 8)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ k ≥ K₀,
      VWZClique.countsWithin k ((OAI.MatrixMultiplication.Arithmetic.omega ℂ - δ) * (k : ℝ) / 3) := by sorry
