-- Prove2me | Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
-- name    : ResidualGaloisRep.charpoly_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/319daa7a-2fc4-5496-bfb9-7fa5d05569ae
-- title:
--   Characteristic polynomials under base change of residual representations
-- statement:
--   Let $k$ and $k'$ be fields, $\psi : k \to k'$ a ring homomorphism, and $\rho$ a residual Galois representation over $k$, that is: a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\rho$ from the group $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\mathrm{End}_k(V)$, together with the condition that $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ with $\mathbb{Q} \subseteq L \subseteq \overline{\mathbb{Q}}$, finite-dimensional over $\mathbb{Q}$, such that $\rho(\sigma) = 1$ for every $\sigma$ fixing $L$ pointwise. Let $\sigma$ be any such automorphism of $\overline{\mathbb{Q}}$. The base change of $\rho$ along $\psi$ is formed by viewing $k'$ as a $k$-algebra via $\psi$, replacing $V$ by $k' \otimes_k V$ and each $\rho(\tau)$ by its $k'$-linear base change. The assertion is that the characteristic polynomial of the base-changed endomorphism at $\sigma$, an element of $k'[X]$, equals the image under $\psi$, applied coefficientwise, of the characteristic polynomial of $\rho(\sigma)$ in $k[X]$.
--
--   This is the compatibility of characteristic polynomials with base change, specialised to the two-dimensional residual Galois representations of the project; it allows traces and determinants of a $\sigma$ (in particular of a Frobenius element) to be computed over a small field of coefficients and then transported to any extension. It is used throughout the comparison of mod-$p$ representations attached to elliptic curves with representations over larger fields of the same characteristic carrying Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_charpoly_baseChangeAlong.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ResidualGaloisRep.charpoly_baseChangeAlong {k : Type} [Field k] {k' : Type} [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly ((ρ.baseChangeAlong ψ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map ψ := by sorry
