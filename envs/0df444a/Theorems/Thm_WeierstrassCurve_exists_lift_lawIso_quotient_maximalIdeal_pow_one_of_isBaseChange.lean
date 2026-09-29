-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange
-- name    : WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/f824028f-4ef3-5aa7-808b-872a4ad69945
-- title:
--   Base step of Serre–Tate lifting modulo 𝔪_T
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. (with the ideal $\bot$ declared as the ambient ideal) there is a unit power series $u$ with $\mathrm{nthSeries}\,q = u \cdot \mathrm{drinfeldDivisor}\,q\,0\,0$. Let $W_0$ be a complete discrete valuation domain, adically complete for its maximal ideal, with $\mathfrak{m}_{W_0} = (q)$, equipped with a surjection $\mathrm{res}_0 : W_0 \to k$ of kernel $\mathfrak{m}_{W_0}$. Let $T$ be an Artinian local $W_0$-algebra with a surjection $\mathrm{res}_T : T \to k$ of kernel $\mathfrak{m}_T$ compatible with $\mathrm{res}_0$, and let $G$ be a commutative formal group law over $T$ which is a lift of $E_0$'s, in the sense that $E_0.\mathrm{formalGroup}$ is obtained from $G$ by applying $\mathrm{res}_T$ coefficientwise. The assertion: there exist a Weierstrass curve $E$ over $T$ with $E$ reduced along $\mathrm{res}_T$ equal to $E_0$, a formal group $G_n$ over $T/\mathfrak{m}_T^1$ whose underlying series is the formal group law $\mathrm{formalGroupLawFixed}$ of $E$ reduced modulo $\mathfrak{m}_T^1$, and an isomorphism $\psi$ of formal group laws from $G_n$ to $G$ reduced modulo $\mathfrak{m}_T^1$, such that for every $m$ the coefficient $\mathrm{coeff}_m \psi$ minus $\delta_{m,1}$ lies in the image of $\mathfrak{m}_T$ in $T/\mathfrak{m}_T^1$.
--
--   This is the base case $n = 1$ of the Serre–Tate lifting induction, where the exponent $1$ makes $T/\mathfrak{m}_T^1 \cong k$ and the congruence condition on $\psi$ is vacuous. It feeds the assembly [`WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing`](thm.html#WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing), which proceeds by induction on the nilpotency index of $\mathfrak{m}_T$ through small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange.lean

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

theorem WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup)
    :
    ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ 1))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ 1))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ 1)))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ 1)) := by sorry
