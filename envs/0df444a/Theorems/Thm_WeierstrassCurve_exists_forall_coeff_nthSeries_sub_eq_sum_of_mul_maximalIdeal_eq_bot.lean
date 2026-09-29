-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
-- name    : WeierstrassCurve.exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/6d484cb9-423a-5c52-963e-c8d8f4c86a78
-- title:
--   Universal linear form for the variation of [q] in coefficient q
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $E_0$ a Weierstrass curve over $k$ that is elliptic. The assertion is that there is a tuple $c : \mathrm{Fin}\,5 \to k$ of constants, depending on $E_0$ alone, with the following property. Let $T$ be a commutative local ring, $I \subseteq T$ an ideal with $I \cdot \mathfrak m_T = 0$ and $I \subseteq \mathfrak m_T$, and $\mathrm{res}_T : T \to k$ a surjective ring homomorphism with kernel $\mathfrak m_T$. Let $E, E'$ be Weierstrass curves over $T$ such that $E$ reduces to $E_0$ along $\mathrm{res}_T$ and such that $E$ and $E'$ have the same image under the quotient map $T \to T/I$. Let $G, G'$ be formal group laws over $T$ whose underlying two-variable power series are the explicit Weierstrass formal group laws `formalGroupLawFixed` of $E$ and of $E'$ respectively, obtained by substituting the series $\mathtt{fgZ3Fixed}$ into $\mathtt{fgInv}$. Finally let $t : \mathrm{Fin}\,5 \to T$ be any lift of $c$, i.e. $\mathrm{res}_T(t_i) = c_i$ for all $i$. Then, writing $[q]$ for the $q$-fold iterate `nthSeries q` defined by $[0] = 0$ and $[n+1] = F(\,[n],X\,)$, one has $$\mathrm{coeff}_q\,[q]_{G'} - \mathrm{coeff}_q\,[q]_{G} = t_0(a_1' - a_1) + t_1(a_2' - a_2) + t_2(a_3' - a_3) + t_3(a_4' - a_4) + t_4(a_6' - a_6),$$ where $a_i$ and $a_i'$ are the Weierstrass coefficients of $E$ and $E'$.
--
--   This records the first-order variation, along a square-zero thickening, of the coefficient of $Z^q$ in the multiplication-by-$q$ series of the formal group of a Weierstrass curve: it is a universal $k$-linear form in the increments of the Weierstrass coefficients, with coefficients depending only on the reduction $E_0$. It is used in the small-extension steps of the Serre–Tate type deformation argument, being cited by [`WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot) and by the two variable-change lemmas [`WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot) and its prime variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot.lean

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

theorem WeierstrassCurve.exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (E₀ : WeierstrassCurve k) [E₀.IsElliptic] :
    ∃ c : Fin 5 → k,
      ∀ (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T), I * maximalIdeal T = ⊥ → I ≤ maximalIdeal T →
      ∀ (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
      ∀ (E E' : WeierstrassCurve T), E.map resT = E₀ → E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) →
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed → G'.toPowerSeries = E'.formalGroupLawFixed →
      ∀ (t : Fin 5 → T), (∀ i, resT (t i) = c i) →
        PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) =
          t 0 * (E'.a₁ - E.a₁) + t 1 * (E'.a₂ - E.a₂) + t 2 * (E'.a₃ - E.a₃) + t 3 * (E'.a₄ - E.a₄) +
            t 4 * (E'.a₆ - E.a₆) := by sorry
