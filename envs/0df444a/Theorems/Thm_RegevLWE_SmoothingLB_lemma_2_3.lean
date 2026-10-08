-- Prove2me | Theorems.Thm_RegevLWE_SmoothingLB_lemma_2_3
-- name    : RegevLWE.SmoothingLB.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:58.780518+00:00
-- url     : https://prove2.me/theorems/fff6dd2e-1785-4a1d-993c-1987939add63
-- title:
--   Lemma 2.3 (Banaszczyk's transference theorem) — 1 ≤ λ₁(L)·λ_n(L*) ≤ n
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice of dimension $n \ge 1$, with dual lattice $L^*$. Write $\lambda_1(L)$ for the length of a shortest nonzero vector of $L$ and $\lambda_n(L^*)$ for the smallest $r$ such that $L^*$ contains $n$ linearly independent vectors of length at most $r$. Then
--   $$1 \;\le\; \lambda_1(L)\cdot\lambda_n(L^*) \;\le\; n .$$
--
--   This is Banaszczyk's transference theorem (Math. Ann. 296 (1993), Theorem 2.1), which the paper cites without proof, remarking that the lower bound is easy. The upper bound relates the geometry of a lattice to that of its dual up to a factor linear in the dimension; applied to the lattice $L^*$ (whose dual is $L$) it gives the second inequality of Claim 2.13.
--
--   **Formalization Note** The hypothesis $0 < n$ is the paper's convention that an $n$-dimensional lattice has $n \ge 1$. Both bounds are stated, as printed.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:18, Lemma 2.3 (Banaszczyk 1993, Theorem 2.1)

import Mathlib
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

namespace RegevLWE.SmoothingLB

theorem lemma_2_3 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    1 ≤ lambda1 L * lambdaN (RegevLWE.GaussConv.dual L) ∧ lambda1 L * lambdaN (RegevLWE.GaussConv.dual L) ≤ n := by sorry

end RegevLWE.SmoothingLB
