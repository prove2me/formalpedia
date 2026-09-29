-- Prove2me | Theorems.Thm_Polynomial_squarefree_of_squarefree_map
-- name    : Polynomial.squarefree_of_squarefree_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/43d0135e-95c9-5346-97d1-698a9e4b3a6a
-- title:
--   Squarefreeness descends along a map from a field into a domain
-- statement:
--   Let $\kappa$ be a field and $L$ a commutative ring that is an integral domain, let $\varphi : \kappa \to L$ be a ring homomorphism, and let $f \in \kappa[X]$ be a polynomial. The hypothesis is that the image $f^{\varphi} \in L[X]$, obtained by applying $\varphi$ to the coefficients of $f$, is squarefree in $L[X]$, in the sense that every $h \in L[X]$ with $h^2 \mid f^{\varphi}$ is a unit. The conclusion is that $f$ itself is squarefree in $\kappa[X]$: every $g \in \kappa[X]$ with $g^2 \mid f$ is a unit of $\kappa[X]$. Thus squarefreeness is reflected, not merely preserved, along coefficientwise extension by any ring homomorphism out of a field into a domain; no further hypotheses (separability, injectivity beyond what the source being a field forces, or flatness) are imposed.
--
--   An elementary descent statement for squarefreeness of one-variable polynomials, used to transfer squarefreeness proved over a large field back along a ring map, for instance from an algebraically closed function field to a residue field contained in it. It is invoked in the proofs that the tensored chart algebras [`ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor`](thm.html#ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor) and [`ModularCurve.IgusaScheme.isReduced_chartAlgInf_tensor`](thm.html#ModularCurve.IgusaScheme.isReduced_chartAlgInf_tensor) are reduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_squarefree_of_squarefree_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Polynomial.squarefree_of_squarefree_map {κ L : Type*} [Field κ] [CommRing L] [IsDomain L]
    (φ : κ →+* L) {f : Polynomial κ} (hf : Squarefree (f.map φ)) : Squarefree f := by sorry
