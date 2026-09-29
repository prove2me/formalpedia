-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
-- name    : ResidualGaloisRep.exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/eff37d5d-74ed-5bec-9ee8-8fb0ca4d2543
-- title:
--   Vanishing traces at ℓ ≡ 2 (mod 3) force a stable line
-- statement:
--   Let $k$ be a field of characteristic $3$ and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ of dimension $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, to $\mathrm{End}_k(V)$, which factors through a finite level in the sense that some intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $[L:\mathbb{Q}]$ finite has the property that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma) = 1$. Let $n \colon \mathbb{N} \to \mathbb{Z}$ be a function and $S$ a finite set of naturals. Assume: (i) for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\mathrm{tr}\,\rho(\sigma) = n(\ell)$ in $k$; and (ii) for every prime $\ell \notin S$ with $\ell \equiv 2 \pmod 3$, the image of $n(\ell)$ in $k$ is $0$ (equivalently $3 \mid n(\ell)$). The conclusion is the negation of the following assertion: for every field $K$ that is a $k$-algebra, every subgroup $G$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of index $2$ and every $K$-submodule $W$ of $K \otimes_k V$ stable under all base-changed operators $\rho(\sigma) \otimes \mathrm{id}$ for $\sigma \in G$, one has $W = 0$ or $W = K \otimes_k V$. Thus some extension $K/k$, some index-two subgroup $G$ and some $G$-stable $K$-submodule of $K \otimes_k V$ which is neither zero nor everything exist; since $\dim_K (K \otimes_k V) = 2$, such a submodule is a $G$-stable line.
--
--   This is the characteristic $3$ incarnation of Serre's dihedral-image criterion: Frobenius traces that vanish at all primes inert in $\mathbb{Q}(\sqrt{-3})$ force the representation to become reducible on an index-two subgroup after extension of scalars. It is stated as the negation of an absolute-irreducibility-on-index-two-subgroups hypothesis, and in this form it is used in the analysis of mod $3$ Hecke eigensystems on $H^1$, in [`HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three`](thm.html#HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (n : ℕ → ℤ) (S : Set ℕ) (hS : S.Finite)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (h0 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ℓ ≡ 2 [MOD 3] → (n ℓ : k) = 0) :
    ¬ ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤ := by sorry
