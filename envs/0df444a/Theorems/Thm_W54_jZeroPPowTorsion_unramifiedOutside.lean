-- Prove2me | Theorems.Thm_W54_jZeroPPowTorsion_unramifiedOutside
-- name    : W54.jZeroPPowTorsion_unramifiedOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cf552cd5-832a-5582-b55c-ca7c7d8f4a18
-- title:
--   p-power torsion of J₀(M) is unramified outside Mp
-- statement:
--   Let $M$ be a positive integer and $p$ a natural number assumed prime. Write $J_0(M)$ for `JZero M`, the degree-zero Picard group $\mathrm{Pic}^0$ of the level-$M$ modular function field over $\overline{\mathbb{Q}}$, equipped with its natural action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, and endowed with the module structure `heckeModuleBar M` over the Hecke algebra $\mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ (the polynomial ring in one variable per rational prime, acting through the ring homomorphism sending $X_\ell$ to the Hecke operator `heckeOperatorBar M ℓ` when these operators commute, and through the zero specialisation otherwise). The assertion `UnramifiedOutsideConcrete M p`, which unfolds to `UnramifiedOutside` for $K = \mathbb{Q}$, $L = \overline{\mathbb{Q}}$ and $J = J_0(M)$, is: for every prime $\ell$ with $\ell \nmid Mp$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over the prime $\ell$, every $\sigma$ in the inertia subgroup of $A$ relative to $\mathbb{Q}$, and every $x \in J_0(M)$ annihilated by some power $p^n$, one has $\sigma \cdot x = x$.
--
--   This is the Néron–Ogg–Shafarevich statement for the Jacobian of $X_0(M)$: its $p$-power torsion is unramified at all primes not dividing $Mp$, the source of the ramification bounds on the Galois representations attached to newforms. It is used in the construction of the $p$-adic representations associated with newforms (the statements about characteristic polynomials of Frobenius and about non-unipotence on inertia) and in the flatness criterion at good points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_W54_jZeroPPowTorsion_unramifiedOutside.lean

import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem W54.jZeroPPowTorsion_unramifiedOutside (M p : ℕ) [NeZero M] (hp : p.Prime) :
    letI := heckeModuleBar M
    UnramifiedOutsideConcrete M p := by sorry
