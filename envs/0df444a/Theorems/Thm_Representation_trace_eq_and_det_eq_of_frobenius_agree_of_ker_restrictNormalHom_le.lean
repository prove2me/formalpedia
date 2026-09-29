-- Prove2me | Theorems.Thm_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
-- name    : Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/bbcc07ff-258b-5606-84e7-988224a5bef8
-- title:
--   Frobenius density: traces and determinants agree everywhere
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra, let $V_1$ be a $k$-vector space and $V_2$ a $K$-vector space, and let $\rho_1$ and $\rho_2$ be representations of $G_{\mathbb Q} = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) on $V_1$ over $k$ and on $V_2$ over $K$, with $\dim_k V_1 = \dim_K V_2 = 2$. Let $F$ be a number field, Galois over $\mathbb Q$, realised inside $\overline{\mathbb Q}$ as a $\mathbb Q$-subextension, and assume the kernel of the restriction homomorphism $G_{\mathbb Q} \to \mathrm{Gal}(F/\mathbb Q)$ is contained in $\ker \rho_1 \sqcap \ker \rho_2$, so that both representations factor through $\mathrm{Gal}(F/\mathbb Q)$. Let $S$ be a finite set of natural numbers, and assume that for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $A$, and every $\tau \in G_{\mathbb Q}$ lying in the decomposition subgroup of $A$ over $\mathbb Q$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\mathrm{tr}\,\rho_1(\tau) = \mathrm{tr}\,\rho_2(\tau)$ and $\det \rho_1(\tau) = \det \rho_2(\tau)$, the left-hand sides being transported along $k \to K$. Then for every $\sigma \in G_{\mathbb Q}$ both $\mathrm{tr}\,\rho_1(\sigma) = \mathrm{tr}\,\rho_2(\sigma)$ and $\det \rho_1(\sigma) = \det \rho_2(\sigma)$ hold in $K$.
--
--   This is the density step in the identification of the mod-$p$ representation of a Frey curve with the residual representation attached to a congruent eigenform: agreement of characteristic polynomials of Frobenius outside a finite set of primes propagates, via Frobenius's density theorem for the finite Galois extension through which both representations factor, to agreement of traces and determinants on all of $G_{\mathbb Q}$. It is cited in the construction of the canonical model congruence for a Frey package and in the transfer of support for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
    {k K : Type} [Field k] [Field K] [Algebra k K]
    {V₁ : Type} [AddCommGroup V₁] [Module k V₁] {V₂ : Type} [AddCommGroup V₂] [Module K V₂]
    (ρ₁ : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V₁)
    (ρ₂ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V₂)
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank K V₂ = 2)
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρ₁.ker ⊓ ρ₂.ker)
    (S : Finset ℕ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap k K (LinearMap.trace k V₁ (ρ₁ τ)) = LinearMap.trace K V₂ (ρ₂ τ))
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap k K (LinearMap.det (ρ₁ τ)) = LinearMap.det (ρ₂ τ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    algebraMap k K (LinearMap.trace k V₁ (ρ₁ σ)) = LinearMap.trace K V₂ (ρ₂ σ) ∧
      algebraMap k K (LinearMap.det (ρ₁ σ)) = LinearMap.det (ρ₂ σ) := by sorry
