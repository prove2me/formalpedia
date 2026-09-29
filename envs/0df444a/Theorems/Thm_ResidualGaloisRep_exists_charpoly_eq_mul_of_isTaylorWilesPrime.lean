-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime
-- name    : ResidualGaloisRep.exists_charpoly_eq_mul_of_isTaylorWilesPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/890e4a91-abfc-5a2b-b58e-93394954228a
-- title:
--   Distinct split eigenvalues of Frobenius at a Taylor–Wiles prime
-- statement:
--   Let $k$ be a field and let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\,\mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\,\mathbb{Q}$ to $\mathrm{End}_k(V)$ which is trivial on the automorphisms fixing some finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$ pointwise. Let $L_0$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is a number field and Galois over $\mathbb{Q}$, let $b$ be a basis of $V$ indexed by $\mathrm{Fin}\,2$, and let $\rho_{\mathrm{mat}} : (L_0 \simeq_{\mathbb{Q}} L_0) \to \mathrm{Mat}_{2\times 2}(k)$ be a monoid homomorphism such that for every $\sigma$ in the absolute Galois group, $\rho_{\mathrm{mat}}$ applied to the restriction of $\sigma$ to $L_0$ is the matrix of $\bar\rho.\rho(\sigma)$ in the basis $b$. Let $p, n, q$ be natural numbers such that: $q$ is prime, $q \equiv 1 \pmod{p^n}$, and for every prime ideal $Q$ of $\mathcal{O}_{L_0}$ lying over the ideal $(q)$ of $\mathbb{Z}$ with finite residue ring, the matrix $\rho_{\mathrm{mat}}$ of the arithmetic Frobenius at $Q$ admits $\alpha \neq \beta$ in $k$ with trace $\alpha + \beta$ and determinant $\alpha\beta$; and suppose $\bar\rho$ is unramified at $q$, meaning that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ and every $\sigma$ in the image of the inertia subgroup of $A$ over $\mathbb{Q}$ inside the full Galois group, $\bar\rho.\rho(\sigma) = 1$. Then for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$ and every $\varphi$ in the decomposition subgroup of $P$ over $\mathbb{Q}$ acting on the residue field of $P$ by $x \mapsto x^q$, there exist $\alpha \neq \beta$ in $k$ with $\mathrm{charpoly}(\bar\rho.\rho(\varphi)) = (X - \alpha)(X - \beta)$.
--
--   This is the local condition imposed on the auxiliary primes of the Taylor–Wiles method: at a Taylor–Wiles prime $q$ at which $\bar\rho$ is unramified, the image of any Frobenius element above $q$ has split characteristic polynomial with two distinct roots, so that the local deformation problem at $q$ decomposes according to the two eigenvalues. It is used in the construction of sets of Taylor–Wiles primes avoiding a prescribed finite set, via [`ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed`](thm.html#ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_charpoly_eq_mul_of_isTaylorWilesPrime.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem ResidualGaloisRep.exists_charpoly_eq_mul_of_isTaylorWilesPrime
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L₀] [IsGalois ℚ L₀]
    (b : Module.Basis (Fin 2) k ρbar.V) (ρmat : TaylorWiles.ResidualRep (↥L₀) k)
    (hρmat : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ) = LinearMap.toMatrix b b (ρbar.ρ σ))
    (p n q : ℕ) (htw : TaylorWiles.IsTaylorWilesPrime ρmat p n q) (hunr : ρbar.IsUnramifiedAt q) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
        ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by sorry
