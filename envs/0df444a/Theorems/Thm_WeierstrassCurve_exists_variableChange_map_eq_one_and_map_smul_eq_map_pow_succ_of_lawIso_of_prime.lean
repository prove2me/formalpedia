-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso_of_prime
-- name    : WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/39c07ad8-5a9a-5d2c-b7c0-115de10c26ca
-- title:
--   Serre–Tate uniqueness: improving a variable change from 𝔪ⁿ to 𝔪ⁿ⁺¹
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $E_0$ an elliptic Weierstrass curve over $k$ whose formal group $E_0.\mathtt{formalGroup}$ satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`: taking the distinguished ideal to be $\bot$, there is a unit power series $u$ with the $q$-th series of the formal group equal to $u$ times its Drinfeld divisor at the parameters $0,0$. Let $T$ be an Artinian local commutative ring and $\mathrm{res}_T : T \to k$ a surjective ring homomorphism whose kernel is the maximal ideal of $T$. Let $E, E'$ be Weierstrass curves over $T$ both reducing to $E_0$ along $\mathrm{res}_T$, and let $G, G'$ be commutative formal groups over $T$ whose underlying two-variable power series are the formal group laws $E.\mathtt{formalGroupLawFixed}$ and $E'.\mathtt{formalGroupLawFixed}$ respectively. Let $\psi$ be a `LawIso` from $G$ to $G'$, that is a one-variable power series with vanishing constant term and invertible linear coefficient satisfying the homomorphism identity $\psi(G(X_0,X_1)) = G'(\psi(X_0),\psi(X_1))$, and assume every coefficient of $\psi$ reduces under $\mathrm{res}_T$ to the corresponding coefficient of $X$, i.e. to $1$ in degree $1$ and to $0$ otherwise. Finally let $n \ge 1$ and let $C$ be a Weierstrass variable change over $T$ reducing to the identity modulo the maximal ideal, such that $C \cdot E$ and $E'$ have equal reductions modulo $\mathfrak m_T^{\,n}$. Then there exists a variable change $C'$ over $T$, again reducing to the identity modulo the maximal ideal, with $C' \cdot E$ and $E'$ having equal reductions modulo $\mathfrak m_T^{\,n+1}$.
--
--   This is the inductive step in the uniqueness half of the Serre–Tate theory of local moduli for supersingular elliptic curves: a $\star$-isomorphism of the formal groups of two lifts forces the lifts to be isomorphic, obtained by successively improving a variable change from accuracy $\mathfrak m^n$ to $\mathfrak m^{n+1}$. It feeds the statement over a general Artinian local base, [`WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing_of_prime`](thm.html#WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing_of_prime), by induction on the nilpotency index of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso_of_prime.lean

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

theorem WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso_of_prime
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
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
