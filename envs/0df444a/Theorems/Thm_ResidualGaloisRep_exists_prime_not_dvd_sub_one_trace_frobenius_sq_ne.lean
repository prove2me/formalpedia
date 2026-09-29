-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
-- name    : ResidualGaloisRep.exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/9d2b7b07-81dd-5aa4-a086-eff58bc8e1ef
-- title:
--   Existence of an auxiliary prime for Taylor–Wiles systems
-- statement:
--   Let $k$ be a field, $p$ a prime with $p \neq 2$, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ of rank $2$ together with a monoid homomorphism $\bar\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_k(V)$ (the Galois group taken as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) that is trivial on the automorphisms fixing some finite-dimensional intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$. Assume: $\bar\rho$ is absolutely irreducible, i.e. the base change to $\overline{k} \otimes_k V$ has no Galois-stable submodule besides $\bot$ and $\top$; the associated $p$-adic-style datum has cyclotomic determinant, i.e. $p$ lies in the maximal ideal of $k$ and for all $n$, $\sigma$ and $a$ with $\sigma\mu = \mu^{a}$ for every $p^n$-th root of unity $\mu$ one has $\det \bar\rho(\sigma) - a \in (p^n) \subseteq k$; and the condition `hTW`: for every field $K$ that is a $k$-algebra, every index-$2$ subgroup $G$ of the Galois group and every $K$-submodule of $K \otimes_k V$ stable under $\bar\rho(\sigma)$ for all $\sigma \in G$ is $\bot$ or $\top$. Assume further that $\bar\rho$ is unramified at every prime outside a finite set $S_{\mathrm{ram}} \subseteq \mathbb{N}$, unramifiedness at $q$ meaning that $\bar\rho(\sigma) = 1$ for every $\sigma$ in the inertia subgroup of any valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $q \in A$ a nonunit. Then for every finite set $T \subseteq \mathbb{N}$ there is a prime $r \notin T$ with $p \nmid r - 1$, such that $\bar\rho$ is unramified at $r$ and, for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $r \in P$ a nonunit and every $\sigma$ lying in the decomposition group of $P$ and acting on the residue field of $P$ by $x \mapsto x^{r}$, one has $\mathrm{tr}\,\bar\rho(\sigma)^2 \neq (r+1)^2$ in $k$.
--
--   This is the existence of the auxiliary prime used to rigidify the deformation and Hecke-theoretic situation in the Taylor–Wiles argument: a prime $r \not\equiv 1 \bmod p$ at which $\bar\rho$ is unramified and at which the ratio of the eigenvalues of $\bar\rho(\mathrm{Frob}_r)$ is neither $r$ nor $r^{-1}$ (equivalently, since the determinant is cyclotomic, $\mathrm{tr}^2 \neq (r+1)^2$). It is invoked in the construction of the level-raising and Taylor–Wiles Hecke modules and in the corresponding presentation and bijectivity statement for local Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne.lean

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem ResidualGaloisRep.exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (Sram : Finset ℕ) (hram : ∀ q : ℕ, q.Prime → q ∉ Sram → ρbar.IsUnramifiedAt q)
    (T : Finset ℕ) :
    ∃ r : ℕ, r.Prime ∧ r ∉ T ∧ ¬ p ∣ r - 1 ∧ ρbar.IsUnramifiedAt r ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : k) + 1) ^ 2 := by sorry
