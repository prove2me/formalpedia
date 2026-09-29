-- Prove2me | Theorems.Thm_WeierstrassCurve_VariableChange_eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing
-- name    : WeierstrassCurve.VariableChange.eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/34057b91-6648-5093-b205-ceb078881f9d
-- title:
--   Rigidity of Weierstrass variable changes over Artinian local rings
-- statement:
--   Let $k$ be a field and let $T$ be a commutative ring that is local and Artinian, with maximal ideal $\mathfrak m$. Suppose given a surjective ring homomorphism $\mathrm{res}_T : T \to k$ whose kernel is exactly $\mathfrak m$, so that $k$ is the residue field of $T$. Let $E$ be a Weierstrass curve over $T$ whose discriminant $\Delta$ is a unit of $T$, and let $C = (u, r, s, t)$, with $u \in T^\times$ and $r, s, t \in T$, be a Weierstrass variable change over $T$. Assume that the variable change obtained by applying $\mathrm{res}_T$ coefficientwise to $C$ is the identity variable change over $k$, and that $C$ fixes $E$, i.e. $C \bullet E = E$ as Weierstrass curves over $T$. Then $C$ is the identity variable change, that is, $u = 1$ and $r = s = t = 0$.
--
--   This is the rigidity statement underlying Serre–Tate style deformation arguments in Weierstrass coordinates: a smooth Weierstrass curve over an Artinian local ring admits no nontrivial automorphisms (as a Weierstrass equation) that are congruent to the identity modulo the maximal ideal. It is used in the construction of Drinfeld bases and level structures on modular curves, in the two statements producing an algebra homomorphism and equivalence for $\Gamma_0$-power and rigid-data level data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_VariableChange_eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem WeierstrassCurve.VariableChange.eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing
    (k : Type) [Field k]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E : WeierstrassCurve T) (hE : IsUnit E.Δ)
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1) (hCE : C • E = E) :
    C = 1 := by sorry
