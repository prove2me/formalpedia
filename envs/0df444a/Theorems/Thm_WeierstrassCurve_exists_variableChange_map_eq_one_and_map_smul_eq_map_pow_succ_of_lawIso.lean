-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
-- name    : WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/6257af50-d47e-5b60-99f2-7cd2d08b18f4
-- title:
--   One induction step of Serre–Tate uniqueness of lifts
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group $E_0.\mathrm{formalGroup}$ is Drinfeld-basic in the adic sense for the ideal $\bot$, with parameters $q$ and $x_0 = x_1 = 0$: that is, its $q$-th series is a unit multiple of its Drinfeld divisor $\mathrm{drinfeldDivisor}\ q\ 0\ 0$. Let $T$ be an Artinian local commutative ring together with a surjective ring homomorphism $\mathrm{resT} : T \to k$ whose kernel is the maximal ideal of $T$. Let $E, E'$ be Weierstrass curves over $T$ both reducing to $E_0$ along $\mathrm{resT}$, and let $G, G'$ be commutative formal group laws over $T$ whose underlying two-variable power series are $E.\mathrm{formalGroupLawFixed}$ and $E'.\mathrm{formalGroupLawFixed}$ respectively. Let $\psi$ be an isomorphism of formal group laws $G \to G'$, i.e. a power series with vanishing constant term and invertible linear coefficient satisfying the homomorphism identity $\psi(G(X_0,X_1)) = G'(\psi(X_0),\psi(X_1))$, and assume that $\psi$ reduces to $X$: $\mathrm{resT}$ of its $m$-th coefficient is $1$ for $m = 1$ and $0$ otherwise. Finally let $n \geq 1$ and let $C$ be a Weierstrass variable change over $T$ reducing to the identity along $\mathrm{resT}$ and such that $C \cdot E$ and $E'$ agree modulo $\mathfrak{m}_T^{\,n}$. Then there exists a variable change $C'$ over $T$, again reducing to the identity along $\mathrm{resT}$, such that $C' \cdot E$ and $E'$ agree modulo $\mathfrak{m}_T^{\,n+1}$. The conclusion asserts only the existence of such a $C'$; no compatibility between $C'$ and $C$ modulo $\mathfrak{m}_T^{\,n}$ is claimed.
--
--   This is the inductive step in the uniqueness half of Serre–Tate theory for lifts of a supersingular elliptic curve: an isomorphism of the formal groups of two lifts, trivial modulo the maximal ideal, forces the lifts to be isomorphic by a variable change congruent to the identity, and the congruence is improved one power of $\mathfrak{m}_T$ at a time. It feeds the statement [`WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing`](thm.html#WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing), where the induction over the nilpotency index of $\mathfrak{m}_T$ is carried out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso.lean

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

theorem WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀) (hE' : E'.map resT = E₀)
    (G : FormalGroup T) [G.IsComm] (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) [G'.IsComm] (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0)
    (n : ℕ) (hn : 1 ≤ n)
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1)
    (hCE : (C • E).map (Ideal.Quotient.mk (maximalIdeal T ^ n)) = E'.map (Ideal.Quotient.mk (maximalIdeal T ^ n))) :
    ∃ C' : WeierstrassCurve.VariableChange T, C'.map resT = 1 ∧
      (C' • E).map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) =
        E'.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) := by sorry
