-- Prove2me | Theorems.Thm_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one
-- name    : ResidualGaloisRep.finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/4a2133ab-4243-5dab-83b7-1d322d2753db
-- title:
--   Trace splitting: dim(adρ̄)^G=dim(ad⁰ρ̄)^G+1
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, and let $\bar\rho$ be a residual Galois representation over $k$ in the sense of the project: a $k$-vector space $V$ with $\dim_k V = 2$, together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ over $\mathbb{Q}$ into $\mathrm{End}_k(V)$, which is trivial on the automorphisms fixing some finite-dimensional intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ pointwise. Let $G$ be a group and $\varphi : G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ any group homomorphism. Consider the adjoint representation $\mathrm{adRep}$ of the Galois group on $\mathrm{End}_k(V)$ given by $\sigma \mapsto (f \mapsto \rho(\sigma)\, f\, \rho(\sigma^{-1}))$, and its subrepresentation $\mathrm{adZero}$ on the kernel of $\mathrm{trace}_k : \mathrm{End}_k(V) \to k$. Restricting both along $\varphi$ to representations of $G$, the assertion is that the $k$-dimension of the space of $G$-invariants of $\mathrm{ad}\,\bar\rho$ equals the $k$-dimension of the space of $G$-invariants of $\mathrm{ad}^0\,\bar\rho$ plus one. No finiteness or surjectivity is assumed of $G$ or $\varphi$.
--
--   This is the degree-zero part of the splitting $\operatorname{ad}\bar\rho \cong \operatorname{ad}^0\bar\rho \oplus k$ available when $2$ is invertible, i.e. the comparison of $H^0(G,\operatorname{ad}\bar\rho)$ with $H^0(G,\operatorname{ad}^0\bar\rho)$ for an arbitrary group mapping to the Galois group (for instance a decomposition or inertia group). It is used in [`ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClasses_and_finrank_le), where the local dimension count is carried out for the adjoint representation and transferred to its trace-zero part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem ResidualGaloisRep.finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0)
    {G : Type} [Group G] (φ : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    Module.finrank k (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants =
      Module.finrank k (Rep.res φ ρbar.adZero).ρ.invariants + 1 := by sorry
