-- Prove2me | Theorems.Thm_PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace
-- name    : PrimeSpectrum.apply_eq_apply_of_forall_le_of_connectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/555f36e3-2d14-5020-b9f9-fc72903450e0
-- title:
--   Specialisation-invariant functions on a connected Noetherian spectrum are constant
-- statement:
--   Let $R$ be a commutative ring that is Noetherian and whose prime spectrum $\operatorname{Spec} R$, with the Zariski topology, is connected (and nonempty, as part of `ConnectedSpace`). Let $\alpha$ be an arbitrary type and $\varphi \colon \operatorname{Spec} R \to \alpha$ an arbitrary function, with no continuity or measurability requirement. Assume that $\varphi$ is invariant along the inclusion order of primes: for all points $\mathfrak p, \mathfrak q \in \operatorname{Spec} R$ with $\mathfrak p \le \mathfrak q$, that is $\mathfrak p \subseteq \mathfrak q$, one has $\varphi(\mathfrak p) = \varphi(\mathfrak q)$; equivalently, $\varphi$ takes the same value at a point and at any of its specialisations. The conclusion is that $\varphi$ is constant: for any two primes $\mathfrak p, \mathfrak q \in \operatorname{Spec} R$ one has $\varphi(\mathfrak p) = \varphi(\mathfrak q)$. The statement is given in the form of an implication for a fixed pair $\mathfrak p, \mathfrak q$ universally quantified in the binders, so it is exactly the assertion that $\varphi$ is constant on $\operatorname{Spec} R$.
--
--   This is the standard rigidity principle that an invariant which is constant along specialisations is globally constant on a connected Noetherian base, the topological form of the statement that such an invariant is locally constant. It is used in the construction of the genus of a family of smooth proper curves over a connected Noetherian base, via [`AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem PrimeSpectrum.apply_eq_apply_of_forall_le_of_connectedSpace
    {R : Type u} [CommRing R] [IsNoetherianRing R] [ConnectedSpace (PrimeSpectrum R)]
    {α : Type v} (φ : PrimeSpectrum R → α)
    (h : ∀ p q : PrimeSpectrum R, p ≤ q → φ p = φ q) (p q : PrimeSpectrum R) :
    φ p = φ q := by sorry
