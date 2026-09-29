-- Prove2me | Theorems.Thm_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues
-- name    : TaylorWiles.finrank_inf_traceZero_of_hasDistinctRationalEigenvalues
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/83e810f6-8820-5b00-bb41-34c4705bb12b
-- title:
--   Trace-zero centraliser of a split regular matrix is a line
-- statement:
--   Let $k$ be a field with $2 \neq 0$ in $k$, and let $M$ be a $2 \times 2$ matrix over $k$ satisfying the predicate [`Matrix.HasDistinctRationalEigenvalues`](def/TaylorWiles_Primes.html#L31), which asserts the existence of elements $\alpha, \beta \in k$ with $\alpha \neq \beta$, $\operatorname{tr} M = \alpha + \beta$ and $\det M = \alpha\beta$; equivalently, the characteristic polynomial of $M$ splits over $k$ with two distinct roots. Consider the $k$-linear endomorphism [`TaylorWiles.adAction M`](def/Deformations_TaylorWilesLocal.html#L13) of the matrix algebra $M_2(k)$ given by the difference of left multiplication by $M$ and right multiplication by $M$, that is $X \mapsto MX - XM$, and the submodule [`TaylorWiles.traceZero`](def/Deformations_TaylorWilesLocal.html#L22) defined as the kernel of the trace, viewed as a $k$-linear map $M_2(k) \to k$. The assertion is that the intersection of the kernel of $X \mapsto MX - XM$ (the centraliser of $M$ in $M_2(k)$) with the space of trace-zero matrices is a $k$-vector space of rank $1$.
--
--   This is the linear-algebra form of the first local dimension count at a Taylor–Wiles auxiliary prime $q$: for an unramified residual representation whose Frobenius at $q$ has distinct eigenvalues in the residue field, $\dim H^0(G_q, \mathrm{ad}^0 \bar\rho) = 1$. It is used by [`ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq`](thm.html#ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq), where the matrix is the image of a Frobenius element with prescribed characteristic polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues.lean

import Mathlib
import Definitions.Def_Deformations_TaylorWilesLocal
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module TaylorWiles

universe u

theorem TaylorWiles.finrank_inf_traceZero_of_hasDistinctRationalEigenvalues {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) k} (hM : M.HasDistinctRationalEigenvalues) :
    finrank k (LinearMap.ker (TaylorWiles.adAction M) ⊓ TaylorWiles.traceZero k : Submodule k (Matrix (Fin 2) (Fin 2) k)) = 1 := by sorry
