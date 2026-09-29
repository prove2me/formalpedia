-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot
-- name    : WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/0ea78ac7-0e47-5b1f-9cb9-51eecc53d2b7
-- title:
--   Realising a formal-group lift by a Weierstrass lift
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group law satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. (relative to the ideal $\bot$ of $k$) its $q$-th series `nthSeries q` is a unit of $k[[X]]$ times `drinfeldDivisor q 0 0`. Let $T$ be a local commutative ring with maximal ideal $\mathfrak m$, and $I \subseteq \mathfrak m$ an ideal with $I \cdot \mathfrak m = 0$; let $\mathrm{res}_T : T \to k$ be a surjective ring homomorphism with kernel $\mathfrak m$. Let $G$ be a commutative formal group law over $T$ reducing along $\mathrm{res}_T$ to the formal group law of $E_0$ (that is, $E_0$'s law is the coefficientwise image of $G$'s law), let $E_1$ be a Weierstrass curve over $T$ with $E_1 \otimes_T k = E_0$, and let $G_1$ be a commutative formal group law over $T$ whose power series is $E_1$'s law `formalGroupLawFixed`. Let $\bar G$, $\bar G_1$ be formal group laws over $T/I$ obtained from $G$, $G_1$ by reduction modulo $I$, and let $\bar\psi$ be an isomorphism of formal group laws from $\bar G_1$ to $\bar G$ (a power series over $T/I$ with zero constant term and unit linear coefficient intertwining the two laws) each of whose coefficients is congruent to $\delta_{m,1}$ modulo the image of $\mathfrak m$ in $T/I$. Then there exist a Weierstrass curve $E$ over $T$ with $E \otimes_T T/I = E_1 \otimes_T T/I$, a formal group law $G'$ over $T$ whose power series is $E$'s law `formalGroupLawFixed`, and an isomorphism $\psi$ of formal group laws from $G'$ to $G$ whose coefficients satisfy $\mathrm{res}_T(\mathrm{coeff}_m \psi) = \delta_{m,1}$ for all $m$.
--
--   This is the inductive step of the Serre–Tate style lifting argument in the supersingular case, expressed in Weierstrass coordinates: over a thickening $T$ killed by $I \cdot \mathfrak m = 0$, a formal-group lift $G$ of the formal group of $E_0$ that is isomorphic modulo $I$ to the formal group of a Weierstrass lift $E_1$ is itself, up to isomorphism congruent to the identity, the formal group of a Weierstrass lift $E$ agreeing with $E_1$ modulo $I$. It is used by [`WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists`](thm.html#WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists) to pass from $T/\mathfrak m^n$ to $T/\mathfrak m^{n+1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot.lean

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

theorem WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
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
