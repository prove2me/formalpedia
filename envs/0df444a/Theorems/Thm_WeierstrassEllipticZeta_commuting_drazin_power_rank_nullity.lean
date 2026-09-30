-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_commuting_drazin_power_rank_nullity
-- name    : WeierstrassEllipticZeta.commuting_drazin_power_rank_nullity
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T14:53:31.347953+00:00
-- url     : https://prove2.me/theorems/5b74a7b0-bdd9-485b-a524-86722b722082
-- title:
--   Rank and nullity of matrix powers with a commuting generalized inverse
-- statement:
--   Let $K$ be a field, let $n,d\in\mathbb N$, and let $A,B$ be
--   $n\times n$ matrices over $K$. Assume
--   $$
--   AB=BA,\qquad AB^2=B,\qquad A^{d+1}B=A^d.
--   $$
--   Then for every natural number $N\ge d$,
--   $$
--   \operatorname{rank}(A^N)=\operatorname{rank}(AB),\qquad
--   \dim_K\ker(A^N)=\dim_K\ker(AB).
--   $$
--   The exponent $d$ need not be positive or bounded by $n$. The statement
--   includes $n=0$ and the case $d=N=0$. No characteristic assumption on
--   $K$ is required.
-- source:
--   Derived linear-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. If matrices A and B commute, ABB=B and A^(d+1)B=A^d, then every A^N with N>=d has the rank and nullity of AB. The proof factors AB through A^N and shows that A^N is fixed by multiplication by AB, then uses product-rank inequalities and rank-nullity. Works over every field, including d=0. No Prove2Me theorem dependencies or new definitions.

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Group.Idempotent

theorem WeierstrassEllipticZeta.commuting_drazin_power_rank_nullity
    (K : Type*) [Field K] (n d : ℕ)
    (A B : Matrix (Fin n) (Fin n) K) (hc : Commute A B)
    (h₁ : A * B * B = B) (h₂ : A ^ (d + 1) * B = A ^ d) :
    ∀ N : ℕ, d ≤ N →
      (A ^ N).rank = (A * B).rank ∧
        Module.finrank K (LinearMap.ker (A ^ N).mulVecLin) =
          Module.finrank K (LinearMap.ker (A * B).mulVecLin) := by sorry
