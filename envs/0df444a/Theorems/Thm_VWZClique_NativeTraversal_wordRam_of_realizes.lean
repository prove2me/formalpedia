-- Prove2me | Theorems.Thm_VWZClique_NativeTraversal_wordRam_of_realizes
-- name    : VWZClique.NativeTraversal.wordRam_of_realizes
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T14:07:59.869657+00:00
-- url     : https://prove2.me/theorems/a14b9b9c-677b-4f05-b57e-7f7928123008
-- title:
--   From a realized nine-vertex recursion to faster word-RAM clique counting
-- statement:
--   Suppose the weighted nine-vertex clique recursion has a fixed logarithmic-word RAM program for each sufficiently large clique size $k$. On every sufficiently large input graph, the program must return the recursion's exact value and spend at most its recursive cost times a fixed power of the bit length. If the square multiplication cost satisfies $\mathrm{mm}(n)\le M n^{\omega_{\mathbb C}+\epsilon_{36}/8}$ for every $n\ge1$, where $\epsilon_{36}$ is the saving for nine-vertex patterns with at most 36 edges, then some $\delta>0$ works for all sufficiently large $k$: the number of $k$-cliques can be computed on the word RAM in $O(n^{(\omega_{\mathbb C}-\delta)k/3})$ time.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good, Theorem 1.1 and Appendix A. https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_VWZClique_NativeCliqueCompiler

theorem VWZClique.NativeTraversal.wordRam_of_realizes {mm : ℕ → ℕ} {M : ℝ} (hM : 0 < M)
    (hmm : ∀ n : ℕ, 1 ≤ n → (mm n : ℝ) ≤ M * (n : ℝ) ^
      (OAI.MatrixMultiplication.Arithmetic.omega ℂ +
        (VWZClique.UniformFolds.levelSaving 36).val / 8))
    {T U A : ℕ} (native : VWZClique.NativeTraversal.Realizes mm T U A) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ k ≥ K₀,
      VWZClique.countsWithin k
        ((OAI.MatrixMultiplication.Arithmetic.omega ℂ - δ) * (k : ℝ) / 3) := by sorry
