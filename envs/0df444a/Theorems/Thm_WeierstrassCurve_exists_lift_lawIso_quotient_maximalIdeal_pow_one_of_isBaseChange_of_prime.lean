-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime
-- name    : WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/74cceec7-a3a0-57b9-9545-765f357ef715
-- title:
--   Serre–Tate existence, base step modulo 𝔪_T
-- statement:
--   Fix a prime $q$ and a field $k$ of characteristic $q$, and an elliptic Weierstrass curve $E_0$ over $k$ whose formal group $E_0$`.formalGroup` (the one-variable group law `formalGroupLawFixed` attached to $E_0$) satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with the adic structure on $k$ given by the zero ideal there is a unit power series $u$ with `nthSeries q` $= u \cdot$ `drinfeldDivisor q 0 0` for that group law. Let $W_0$ be a complete discrete valuation domain, complete for its maximal-ideal-adic topology, with $\mathfrak{m}_{W_0} = (q)$, equipped with a surjective ring map $\mathrm{res}_0 : W_0 \to k$ whose kernel is $\mathfrak{m}_{W_0}$. Let $T$ be an Artinian local $W_0$-algebra with a surjective ring map $\mathrm{res}_T : T \to k$ of kernel $\mathfrak{m}_T$ such that $\mathrm{res}_T \circ \mathrm{algebraMap} = \mathrm{res}_0$, and let $G$ be a commutative formal group law over $T$ which is a base change of $E_0$`.formalGroup` along $\mathrm{res}_T$, that is, the power series of $G$ is the coefficientwise image of that of $E_0$`.formalGroup`. The conclusion asserts the existence of a Weierstrass curve $E$ over $T$ with $E$ reducing to $E_0$ coefficientwise under $\mathrm{res}_T$, a formal group law $G_n$ over $T/\mathfrak{m}_T^1$ whose underlying power series is `formalGroupLawFixed` of the reduction of $E$ modulo $\mathfrak{m}_T^1$, and an isomorphism $\psi$ of formal group laws from $G_n$ to the reduction of $G$ modulo $\mathfrak{m}_T^1$ — a power series with zero constant term and invertible linear coefficient satisfying $\psi(G_n(X_0,X_1)) = (G \bmod \mathfrak{m}_T)(\psi(X_0),\psi(X_1))$ — all of whose coefficients are congruent to those of $X$ modulo the image of $\mathfrak{m}_T$ in $T/\mathfrak{m}_T^1$.
--
--   This is the base case, at nilpotency index one, of the Serre–Tate existence argument: over $T/\mathfrak{m}_T \cong k$ any formal group law obtained from $E_0$ by base change is already the formal group law of a Weierstrass lift, with the identity as isomorphism. It feeds the induction over small extensions $\mathfrak{m}^n/\mathfrak{m}^{n+1}$ carried out in [`WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime`](thm.html#WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime.lean

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

theorem WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
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
