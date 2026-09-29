-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong
-- name    : ResidualGaloisRep.exists_basis_monoidHom_toMatrix_eq_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/b57c985c-ad27-5c70-b2be-a955bde471d3
-- title:
--   Matrix model of a base-changed residual Galois representation
-- statement:
--   Let $\psi\colon k\to L$ be a ring homomorphism between fields and let $R$ be a residual Galois representation over $k$, that is: a $k$-vector space $R.V$ with $\dim_k R.V=2$, a monoid homomorphism $R.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)=\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k(R.V)$, and a witness that $R.\rho$ factors through a finite level, i.e. there is an intermediate field $\mathbb Q\subseteq L_0\subseteq\overline{\mathbb Q}$ with $L_0$ finite-dimensional over $\mathbb Q$ such that every $\sigma$ fixing $L_0$ pointwise has $R.\rho(\sigma)=1$. Write $R.\mathrm{baseChangeAlong}\ \psi$ for the residual representation over $L$ on $L\otimes_k R.V$, formed using the $k$-algebra structure on $L$ given by $\psi$, with $\sigma$ acting by the base change of $R.\rho(\sigma)$. The assertion is that there exist a basis $b$ of $L\otimes_k R.V$ indexed by $\mathrm{Fin}\ 2$ and a monoid homomorphism $\rho_M\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{GL}_2(L)$ such that: $\rho_M$ factors through a finite level in the same sense; for every $\sigma$ the underlying matrix of $\rho_M(\sigma)$ is the matrix of $(R.\mathrm{baseChangeAlong}\ \psi).\rho(\sigma)$ in the basis $b$; and for every $\sigma$ the characteristic polynomial of that matrix is the image under $\psi$, coefficientwise, of the characteristic polynomial of the endomorphism $R.\rho(\sigma)$ of $R.V$.
--
--   This is the passage from the bundled form of a two-dimensional residual Galois representation (a rank-two space with a Galois action of finite level) to the matrix form $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{GL}_2(L)$, together with the compatibility of characteristic polynomials under extension of scalars along $\psi$. It is used where inertia eigenvectors and Frobenius characteristic polynomials are handled in matrix coordinates, as in [`GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two`](thm.html#GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.exists_basis_monoidHom_toMatrix_eq_baseChangeAlong
    {k L : Type} [Field k] [Field L] (ψ : k →+* L) (R : ResidualGaloisRep k) :
    ∃ (b : Module.Basis (Fin 2) L (R.baseChangeAlong ψ).V)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρM ∧
      (∀ σ, (ρM σ).val = LinearMap.toMatrix b b ((R.baseChangeAlong ψ).ρ σ)) ∧
      (∀ σ, (ρM σ).val.charpoly = (LinearMap.charpoly (R.ρ σ)).map ψ) := by sorry
