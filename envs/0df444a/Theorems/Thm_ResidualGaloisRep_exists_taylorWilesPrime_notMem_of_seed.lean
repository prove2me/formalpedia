-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_seed
-- name    : ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/1b3a6e00-6cd9-502a-aa28-9ed7ebdfa1d1
-- title:
--   Taylor–Wiles primes avoiding a finite set, in Frobenius form
-- statement:
--   Let $k$ be a field and let $\bar\rho$ be a residual Galois representation over $k$: a $2$-dimensional $k$-vector space $V$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k(V)$ that is trivial on the elements fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$. Let $L_0 \subseteq \overline{\mathbb Q}$ be a number field that is Galois over $\mathbb Q$, let $b$ be a basis of $V$ indexed by $\mathrm{Fin}\,2$, and let $\rho_{\mathrm{mat}} : \mathrm{Gal}(L_0/\mathbb Q) \to \mathrm{GL}$-valued $2\times 2$ matrices over $k$ be a monoid homomorphism such that for every $\sigma$ in the absolute Galois group, $\rho_{\mathrm{mat}}$ of the restriction of $\sigma$ to $L_0$ equals the matrix of $\rho(\sigma)$ in the basis $b$. Let $p, n$ be natural numbers, $S$ a finite set of naturals, and assume given a seed for $\rho_{\mathrm{mat}}$ at $(p,n)$ outside $S$, i.e. an element $\sigma \in \mathrm{Gal}(L_0/\mathbb Q)$ such that $\rho_{\mathrm{mat}}(\sigma)$ has trace $\alpha+\beta$ and determinant $\alpha\beta$ for some $\alpha \neq \beta$ in $k$, and such that every prime $\ell \notin S$ at which $\sigma$ is realised cyclically (some power $\sigma^k$ with $k$ coprime to the order of $\sigma$ is conjugate to the arithmetic Frobenius at every prime of $\mathcal O_{L_0}$ over $\ell$ with finite residue ring) satisfies $\ell \equiv 1 \pmod{p^n}$. Finally let $B$ be a finite set of naturals and assume $\bar\rho$ is unramified at every prime $q \notin B$, in the sense that for every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, every element of the image in the absolute Galois group of the inertia subgroup of $A$ acts as the identity on $V$. The conclusion is that there is a prime $q \notin S$, $q \notin B$, with $q \equiv 1 \pmod{p^n}$, such that $\bar\rho$ is unramified at $q$ in the above sense and, for every valuation subring $P$ of $\overline{\mathbb Q}$ having $q$ as a nonunit and every $\varphi$ in the decomposition subgroup of $P$ acting on the residue field of $P$ by $x \mapsto x^q$, the characteristic polynomial of $\rho(\varphi)$ equals $(X-\alpha)(X-\beta)$ for some $\alpha \neq \beta$ in $k$.
--
--   This is the existence of Taylor–Wiles auxiliary primes $q \equiv 1 \pmod{p^n}$ avoiding a prescribed finite set, recorded at the level of the absolute Galois group: $\bar\rho$ is unramified at $q$ and every Frobenius element above $q$ has distinct eigenvalues in $k$. It feeds the variant in which the seed hypothesis is replaced by absolute irreducibility of $\bar\rho$, which in turn supplies the sets of auxiliary primes used in the Taylor–Wiles patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_seed.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L₀] [IsGalois ℚ L₀]
    (b : Module.Basis (Fin 2) k ρbar.V) (ρmat : TaylorWiles.ResidualRep (↥L₀) k)
    (hρmat : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ) = LinearMap.toMatrix b b (ρbar.ρ σ))
    (p n : ℕ) {S : Finset ℕ} (seed : TaylorWiles.Seed ρmat p n S) (B : Finset ℕ)
    (hunr : ∀ q : ℕ, q.Prime → q ∉ B → ρbar.IsUnramifiedAt q) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ∉ B ∧ q ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by sorry
