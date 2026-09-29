-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
-- name    : WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/921a18a0-4968-5798-997c-d56402db1b0f
-- title:
--   Every element of I realised by a q-series coefficient shift
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $E_0$ a Weierstrass curve over $k$ which is elliptic and whose formal group $E_0$`.formalGroup` — the formal group over $k$ whose underlying two-variable power series is $E_0$`.formalGroupLawFixed` — satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with the ideal $\bot$ declared on $k$ there is a unit $u \in k\llbracket X \rrbracket$ with `nthSeries q` of that formal group equal to $u$ times `drinfeldDivisor q 0 0`; here `nthSeries` is defined by `nthSeries 0 = 0` and `nthSeries (n+1)` = the substitution of (`nthSeries n`, $X$) into the group law. Let $T$ be a commutative local ring with maximal ideal $\mathfrak m$, and $I \subseteq \mathfrak m$ an ideal with $I \cdot \mathfrak m = \bot$; let $\mathrm{res}_T : T \to k$ be a surjective ring homomorphism with kernel $\mathfrak m$. Let $E$ be a Weierstrass curve over $T$ with coefficientwise image $E_0$ under $\mathrm{res}_T$, and let $c \in I$. Then there is a Weierstrass curve $E'$ over $T$ with the same image as $E$ under reduction modulo $I$, such that for all formal groups $G, G'$ over $T$ whose underlying power series are $E$`.formalGroupLawFixed` and $E'$`.formalGroupLawFixed`, the $X^q$-coefficients satisfy $\operatorname{coeff}_q(G'.\mathrm{nthSeries}\,q) - \operatorname{coeff}_q(G.\mathrm{nthSeries}\,q) = c$. Ellipticity of $E'$ is not asserted.
--
--   This is the surjectivity of the first-order (Hasse-type) coordinate in the Serre–Tate style deformation theory used here: over a small extension $T \to T/I$ with $I \cdot \mathfrak m = 0$, every element of $I$ occurs as the change in the $X^q$-coefficient of the $q$-series of the formal group when the Weierstrass curve is varied within its class modulo $I$. The statement is that of [`WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot) with the hypothesis $q \neq 2$ removed, and it feeds the small-extension induction step [`WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime.lean

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

theorem WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E : WeierstrassCurve T) (hE : E.map resT = E₀) (c : T) (hc : c ∈ I) :
    ∃ E' : WeierstrassCurve T, E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) ∧
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed →
        G'.toPowerSeries = E'.formalGroupLawFixed →
          PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) = c := by sorry
