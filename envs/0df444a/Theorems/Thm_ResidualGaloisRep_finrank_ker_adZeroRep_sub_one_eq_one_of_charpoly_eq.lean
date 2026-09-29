-- Prove2me | Theorems.Thm_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
-- name    : ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/ed42b2cf-7ad2-51a1-b37f-fa64553dafb9
-- title:
--   Regular semisimple σ fixes a line in ad⁰ρ̄
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, and let $\bar\rho$ be a residual Galois representation over $k$: that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to $\mathrm{End}_k(V)$ which is trivial on the automorphisms fixing some finite-dimensional intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ pointwise. Let $\sigma$ be such an automorphism, and let $\alpha, \beta \in k$ with $\alpha \neq \beta$ be such that the characteristic polynomial of the endomorphism $\bar\rho(\sigma)$ of $V$ equals $(X - \alpha)(X - \beta)$. The adjoint representation `adRep` sends an automorphism $\tau$ to the endomorphism $f \mapsto \bar\rho(\tau) \, f \, \bar\rho(\tau^{-1})$ of $\mathrm{End}_k(V)$, and `adZeroRep` is its restriction to the subspace of trace-zero endomorphisms, which is stable under this conjugation action. The conclusion is that the kernel of $\mathrm{ad}^0\bar\rho(\sigma) - 1$, a subspace of the trace-zero endomorphisms of $V$, has $k$-dimension exactly $1$.
--
--   This is the local computation, at a Taylor–Wiles prime, of the $\sigma$-invariants in the trace-zero adjoint representation: the centraliser of a regular semisimple element of $\mathfrak{gl}_2$ is the two-dimensional algebra it generates, and intersecting with $\mathfrak{sl}_2$ leaves a line. It is used in the computation of the invariants of $\mathrm{ad}^0\bar\rho$ under the relevant cyclic group and in the bound on the strict Selmer group by the number of Taylor–Wiles primes plus the dimension of the dual Selmer group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZeroMatrixGlue
import Definitions.Def_Deformations_TaylorWilesLocal
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module TaylorWiles

theorem ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {α β : k} (hαβ : α ≠ β)
    (hchar : LinearMap.charpoly (ρbar.ρ σ) = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    Module.finrank k (LinearMap.ker (ρbar.adZeroRep σ - 1)) = 1 := by sorry
