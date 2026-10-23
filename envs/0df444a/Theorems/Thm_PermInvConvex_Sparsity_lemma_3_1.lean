-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_lemma_3_1
-- name    : PermInvConvex.Sparsity.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:54.754431+00:00
-- url     : https://prove2.me/theorems/a72737f4-b27b-4c17-9725-4d45772d271b
-- title:
--   Lemma 3.1, p. 7 — permutation-invariant norms are monotone under majorization
-- statement:
--   Let $f$ be a permutation-invariant norm on $\mathbb R^n$ and let $x, y \in \mathbb R^n$ with $x \ge_m y$ ($x$ majorizes $y$). Then
--   $$f(x) \ge f(y).$$
--
--   The paper quotes this from the literature (its reference [20]); it is the step that turns a majorization relation between vectors into an inequality between their norms, used in the proofs of Theorems 3.1 and 3.2.
--
--   **Formalization Note** $f$ is a function `(Fin n → ℝ) → ℝ` with the norm and permutation-invariance axioms (no sign invariance is required). Majorization is stated through sums of the $j$ largest entries.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 7, Lemma 3.1

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem lemma_3_1 {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsPermInvNorm f)
    (x y : Fin n → ℝ) (hxy : Majorizes x y) :
    f y ≤ f x := by sorry

end PermInvConvex.Sparsity
