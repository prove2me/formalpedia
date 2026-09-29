-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
-- name    : WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/48e1a5be-3046-5610-915b-50528e610052
-- title:
--   Lifting a mod-I isomorphism to a Weierstrass formal group
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$ and $E_0$ an elliptic Weierstrass curve over $k$ whose formal group $E_0$`.formalGroup` satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, that is — with the zero ideal supplying the `WithIdeal` structure — there is a unit $u \in k⟦X⟧$ with $E_0$`.formalGroup.nthSeries q` $= u \cdot{}$`drinfeldDivisor q 0 0`. Let $T$ be a local commutative ring and $I \subseteq T$ an ideal with $I \cdot \mathfrak{m} = 0$ and $I \subseteq \mathfrak{m}$, where $\mathfrak{m} =$ `maximalIdeal T`, and let $\mathrm{res}_T : T \to k$ be a surjective ring homomorphism with kernel $\mathfrak{m}$. Let $G$ be a commutative formal group law over $T$ whose coefficientwise image under $\mathrm{res}_T$ is the formal group law of $E_0$, let $E_1$ be a Weierstrass curve over $T$ with $E_1$`.map resT` $= E_0$, and let $G_1$ be a commutative formal group law over $T$ whose underlying two-variable series is $E_1$`.formalGroupLawFixed`. Let $\bar G$, $\bar G_1$ be formal group laws over $T/I$ obtained from $G$, $G_1$ by coefficientwise reduction modulo $I$, and let $\bar\psi$ be an isomorphism $\bar G_1 \to \bar G$ of formal group laws over $T/I$ — a power series with zero constant term and unit linear coefficient satisfying $\bar\psi(\bar G_1(X_0,X_1)) = \bar G(\bar\psi(X_0),\bar\psi(X_1))$ — all of whose coefficients agree with those of $X$ modulo the image of $\mathfrak{m}$ in $T/I$. Then there exist a Weierstrass curve $E$ over $T$ with $E$`.map (Ideal.Quotient.mk I)` $= E_1$`.map (Ideal.Quotient.mk I)`, a formal group law $G'$ over $T$ whose series is $E$`.formalGroupLawFixed`, and an isomorphism $\psi : G' \to G$ of formal group laws over $T$ such that $\mathrm{res}_T$ applied to the $m$-th coefficient of $\psi$ is $1$ for $m = 1$ and $0$ otherwise.
--
--   This is the inductive step in the Serre–Tate style deformation argument for a supersingular curve over a field of characteristic $q$: an abstract lift $G$ of the formal group which is, modulo a square-zero ideal $I$, isomorphic to the formal group of a Weierstrass lift is itself the formal group of a Weierstrass lift, via an isomorphism congruent to the identity modulo the maximal ideal. It is used by [`WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime`](thm.html#WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime) to pass from the $n$-th to the $(n+1)$-st power of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime.lean

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

theorem WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)

    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup)
    (E₁ : WeierstrassCurve T) (hE₁ : E₁.map resT = E₀)
    (G₁ : FormalGroup T) [G₁.IsComm] (hG₁ : G₁.toPowerSeries = E₁.formalGroupLawFixed)

    (Gbar G₁bar : FormalGroup (T ⧸ I))
    (hGbar : G.IsBaseChange (Ideal.Quotient.mk I) Gbar) (hG₁bar : G₁.IsBaseChange (Ideal.Quotient.mk I) G₁bar)
    (ψbar : FormalGroup.LawIso G₁bar Gbar)
    (hψbar : ∀ m : ℕ, PowerSeries.coeff m ψbar.series - (if m = 1 then 1 else 0) ∈
      (maximalIdeal T).map (Ideal.Quotient.mk I)) :
    ∃ (E : WeierstrassCurve T) (_ : E.map (Ideal.Quotient.mk I) = E₁.map (Ideal.Quotient.mk I))
      (G' : FormalGroup T) (_ : G'.toPowerSeries = E.formalGroupLawFixed) (ψ : FormalGroup.LawIso G' G),
      ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0 := by sorry
