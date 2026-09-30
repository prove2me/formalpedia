-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_idempotent_matrix_support_rank
-- name    : WeierstrassEllipticZeta.idempotent_matrix_support_rank
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T14:35:16.5833+00:00
-- url     : https://prove2.me/theorems/eb43624b-e93d-416b-8284-ec34fa213cf7
-- title:
--   Weighted support rank and nullity of an idempotent matrix
-- statement:
--   Let $K$ be a field of characteristic zero, let $n$ be a natural number,
--   and let $V$ be a finite type. Let $E$ be an $n\times n$ matrix over $K$,
--   let $w:V\to\mathbb N$ be a weight function, and let $f:V\to K$.
--   Assume that $E$ is idempotent and that
--   $$
--   \operatorname{tr}(E)=\sum_{v\in V}w(v)
--   \begin{cases}0,&f(v)=0,\\1,&f(v)\ne0.\end{cases}
--   $$
--   Here each natural weight is mapped to $K$ by its canonical embedding.
--   Writing $S=\{v\in V:f(v)\ne0\}$, one has
--   $$
--   \operatorname{rank}(E)=\sum_{v\in S}w(v),\qquad
--   \dim_K\ker(E)=n-\sum_{v\in S}w(v).
--   $$
--   The subtraction is natural-number subtraction. The hypotheses imply
--   that the supported weight sum is at most $n$. Empty index types,
--   empty support, zero weights and $n=0$ are allowed.
-- source:
--   Derived linear-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. Over a characteristic-zero field, an idempotent matrix whose trace is a sum of natural weights times zero-or-one support values has rank equal to the supported weight sum, and nullity equal to its size minus that sum. Uses the trace formula for projections, injectivity of natural-number casts and rank-nullity. No Prove2Me theorem dependencies or new definitions.

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

open scoped Classical

theorem WeierstrassEllipticZeta.idempotent_matrix_support_rank
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (V : Type*) [Fintype V]
    (E : Matrix (Fin n) (Fin n) K) (w : V → ℕ) (f : V → K)
    (hE : IsIdempotentElem E)
    (htrace : E.trace = ∑ v : V, (w v : K) * (if f v = 0 then 0 else 1)) :
    E.rank = ∑ v ∈ Finset.univ.filter (fun v : V => f v ≠ 0), w v ∧
      Module.finrank K (LinearMap.ker E.mulVecLin) =
        n - ∑ v ∈ Finset.univ.filter (fun v : V => f v ≠ 0), w v := by sorry
