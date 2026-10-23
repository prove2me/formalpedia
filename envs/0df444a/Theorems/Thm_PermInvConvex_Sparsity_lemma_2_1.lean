-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_lemma_2_1
-- name    : PermInvConvex.Sparsity.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:00.02437+00:00
-- url     : https://prove2.me/theorems/0eec7cb6-c300-43c7-a99e-14149cd3ad1f
-- title:
--   Lemma 2.1, p. 3 — a linear map preserving S preserves conv(S)
-- statement:
--   Let $T$ be a real $n \times n$ matrix and $S \subseteq \mathbb R^n$ a set with $Tx \in S$ for every $x \in S$. Then
--   $$x \in \operatorname{conv}(S) \implies Tx \in \operatorname{conv}(S).$$
--
--   Applied to permutation matrices and sign changes, this shows that the convex hull of a permutation-invariant (sign-invariant) set is again permutation-invariant (sign-invariant), which is how the paper transfers the symmetries of $N^K_{\|\cdot\|_s}$ to its convex hull.
--
--   **Formalization Note** $Tx$ is Mathlib's matrix–vector product `T *ᵥ x`.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 3, Lemma 2.1

import Mathlib
open Matrix

namespace PermInvConvex.Sparsity

theorem lemma_2_1 {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (S : Set (Fin n → ℝ))
    (hS : ∀ x ∈ S, T *ᵥ x ∈ S) :
    ∀ x ∈ convexHull ℝ S, T *ᵥ x ∈ convexHull ℝ S := by sorry

end PermInvConvex.Sparsity
