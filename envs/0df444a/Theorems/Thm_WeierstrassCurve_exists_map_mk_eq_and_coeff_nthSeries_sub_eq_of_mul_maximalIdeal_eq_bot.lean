-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
-- name    : WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/dd349afb-f5cb-5af7-b61d-2905d0f3a1cd
-- title:
--   Realising prescribed q-th coefficients of [q] by lifting
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group $E_0.\mathtt{formalGroup}$ (the formal group attached to the two-variable Weierstrass formal group law `formalGroupLawFixed`) satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`: taking the ideal $\bot$ as the ideal of reference, there is a unit $u \in k[[X]]$ with $n$-series $\mathtt{nthSeries}\ q = u \cdot \mathtt{drinfeldDivisor}\ q\ 0\ 0$, where $\mathtt{nthSeries}$ is defined by $\mathtt{nthSeries}\ 0 = 0$ and $\mathtt{nthSeries}(n+1) = F(\mathtt{nthSeries}\ n, X)$, i.e. the multiplication-by-$n$ series; by [`FormalGroup.isDrinfeldBasisAdic_zero_zero_iff`](thm.html#FormalGroup.isDrinfeldBasisAdic_zero_zero_iff) this amounts to $\mathtt{nthSeries}\ q = u\cdot X^{q^2}$. Let $T$ be a commutative local ring and $I \subseteq T$ an ideal with $I \cdot \mathfrak{m}_T = \bot$ and $I \subseteq \mathfrak{m}_T$, let $\mathrm{res}_T : T \to k$ be a surjective ring homomorphism with kernel $\mathfrak{m}_T$, let $E$ be a Weierstrass curve over $T$ with $E$ reducing to $E_0$ along $\mathrm{res}_T$, and let $c \in I$. Then there is a Weierstrass curve $E'$ over $T$ whose coefficients agree with those of $E$ modulo $I$, such that for all formal groups $G, G'$ over $T$ whose underlying series are $E.\mathtt{formalGroupLawFixed}$ and $E'.\mathtt{formalGroupLawFixed}$ respectively, the coefficients of $X^q$ in their $q$-series satisfy $\operatorname{coeff}_q(G'.\mathtt{nthSeries}\ q) - \operatorname{coeff}_q(G.\mathtt{nthSeries}\ q) = c$.
--
--   This is the surjectivity half of the first-order analysis of the Hasse-invariant functional in the Serre–Tate theory of deformations of a supersingular elliptic curve: over a small extension $T$ with $I\cdot\mathfrak m_T = 0$, every element of $I$ occurs as the change in the $X^q$-coefficient of the multiplication-by-$q$ series caused by modifying a Weierstrass lift within its class modulo $I$. It is used by [`WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime) and by [`WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot), the existence and rigidity steps of the deformation-theoretic package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot.lean

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

theorem WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E : WeierstrassCurve T) (hE : E.map resT = E₀) (c : T) (hc : c ∈ I) :
    ∃ E' : WeierstrassCurve T, E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) ∧
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed →
        G'.toPowerSeries = E'.formalGroupLawFixed →
          PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) = c := by sorry
