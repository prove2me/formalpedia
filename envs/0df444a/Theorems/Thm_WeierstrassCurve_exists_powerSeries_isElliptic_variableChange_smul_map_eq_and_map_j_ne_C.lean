-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C
-- name    : WeierstrassCurve.exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/6812d823-7ce7-59a4-a5b9-7d50838c8944
-- title:
--   Elliptic deformations over 𝒪[[T]] with non-constant reduced j
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $k$ an algebraically closed field and $\pi \colon \mathcal{O} \to k$ a surjective ring homomorphism which reflects units (every element of $\mathcal{O}$ whose image under $\pi$ is a unit is itself a unit in $\mathcal{O}$). Let $W$ be a Weierstrass curve over $k$ that is elliptic, i.e. whose discriminant is a unit of $k$. Then there exists a Weierstrass curve $E$ over the power series ring $\mathcal{O}[[T]]$, again elliptic in the sense that its discriminant is a unit of $\mathcal{O}[[T]]$, such that both of the following hold. First, the specialisation of $E$ along the ring homomorphism $\mathcal{O}[[T]] \to k$ given by taking the constant coefficient and then applying $\pi$ is isomorphic to $W$ through a change of Weierstrass coordinates over $k$: there is a variable change $v$ over $k$ with $v \bullet (E \text{ mapped along } \pi \circ \mathrm{constantCoeff}) = W$. Second, the power series $\pi(j(E)) \in k[[T]]$ obtained by reducing the coefficients of the $j$-invariant of $E$ is not the constant power series with its own constant coefficient, i.e. it is non-constant.
--
--   This is the existence of a non-isotrivial elliptic deformation over the formal disc with prescribed special fibre, the family used in the local-moduli approach to Deuring's lifting theorem, where non-constancy of the reduced $j$-invariant guarantees that the generic member of the family is not isogenous to its quotients in the relevant way. It is invoked in the constructions of power series deformations carrying lifted two- and three-torsion subgroups whose Kohel quotients are compared with Vélu quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C {𝒪 : Type*} [CommRing 𝒪] {k : Type*} [Field k] [IsAlgClosed k] (π : 𝒪 →+* k) [IsLocalHom π] (hπ : Function.Surjective π) (W : WeierstrassCurve k) [W.IsElliptic] : ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic), (∃ v : WeierstrassCurve.VariableChange k, v • E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = W) ∧ PowerSeries.map π E.j ≠ PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)) := by sorry
