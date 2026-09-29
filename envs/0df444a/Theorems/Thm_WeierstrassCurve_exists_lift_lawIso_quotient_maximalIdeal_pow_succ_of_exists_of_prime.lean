-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
-- name    : WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/f28c9325-fb60-5a10-9b51-071fdac6b29b
-- title:
--   Serre–Tate lifting step: from 𝔪ⁿ to 𝔪ⁿ⁺¹
-- statement:
--   Fix a prime $q$ and a field $k$ of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group $E_0.\mathrm{formalGroup}$ (the one-parameter formal group whose law is $E_0$'s fixed-variable formal group law `formalGroupLawFixed`) satisfies the Drinfeld-basis condition at the ideal $\bot$ with parameters $q, 0, 0$: there is a unit $u \in k\llbracket X\rrbracket$ with $\mathrm{nthSeries}\ q = u \cdot \mathrm{drinfeldDivisor}\ q\ 0\ 0$ for that formal group. Let $W_0$ be a complete discrete valuation domain, adically complete for its maximal ideal, with $\mathfrak m_{W_0} = (q)$, together with a surjection $\mathrm{res}_0 : W_0 \to k$ whose kernel is $\mathfrak m_{W_0}$. Let $T$ be a local Artinian commutative $W_0$-algebra with a surjection $\mathrm{res}_T : T \to k$ of kernel $\mathfrak m_T$, compatible with $\mathrm{res}_0$ along $W_0 \to T$, and let $G$ be a commutative formal group over $T$ whose reduction satisfies $E_0.\mathrm{formalGroup} = \mathrm{MvPowerSeries.map}\ \mathrm{res}_T\ G$. Let $n \ge 1$. Assume there exist a Weierstrass curve $E$ over $T$ with $E.\mathrm{map}\ \mathrm{res}_T = E_0$, a formal group $G_n$ over $T/\mathfrak m_T^n$ whose law is the formal group law of $E$ reduced mod $\mathfrak m_T^n$, and an isomorphism of formal group laws $\psi : G_n \to G \bmod \mathfrak m_T^n$ (a power series with zero constant term, commuting with the two laws, with unit linear coefficient) all of whose coefficients agree with those of $X$ modulo the image of $\mathfrak m_T$ in $T/\mathfrak m_T^n$. Then the same data exist with $n$ replaced by $n+1$.
--
--   This is the inductive step of the existence half of Serre–Tate local moduli in the form needed here: a Weierstrass lift of $E_0$ over $T$ whose formal group is identified with $G$ modulo $\mathfrak m_T^n$, by an isomorphism congruent to the identity, can be replaced by one with the identification valid modulo $\mathfrak m_T^{n+1}$. It is applied, by induction on the nilpotency index of $\mathfrak m_T$, in [`WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime`](thm.html#WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime), and rests on the small-extension existence step for the ideals $\mathfrak m_T^n/\mathfrak m_T^{n+1}$, which are annihilated by $\mathfrak m_T$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime.lean

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

theorem WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup)
    (n : ℕ) (hn : 1 ≤ n)
    (h : ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ n))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ n))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ n)))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ n))) :
    ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ (n + 1)))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1)))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) := by sorry
