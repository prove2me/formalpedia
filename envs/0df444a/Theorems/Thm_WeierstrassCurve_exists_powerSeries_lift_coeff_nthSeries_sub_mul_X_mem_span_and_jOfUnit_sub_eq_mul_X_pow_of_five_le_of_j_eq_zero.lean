-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero
-- name    : WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/571f9e08-d9a0-5637-bebf-dfeedb0d8a48
-- title:
--   Universal monomial-j deformation at a supersingular point, case j=0
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $k$ be a field of characteristic $q$, and let $E_0$ be a Weierstrass curve over $k$ with invertible discriminant. Assume that $(0,0)$ is a Drinfeld basis of level $q$ for the formal group $\widehat{E_0}$ relative to the ideal $\bot$, that is, the $q$-division series $[q]_{\widehat{E_0}}$ (the $q$-th iterate `nthSeries`) is a unit multiple of `drinfeldDivisor q 0 0`; by [`FormalGroup.isDrinfeldBasisAdic_zero_zero_iff`](thm.html#FormalGroup.isDrinfeldBasisAdic_zero_zero_iff) this says $[q]_{\widehat{E_0}} = u\,Z^{q^2}$ for a unit $u$, i.e. $E_0$ is supersingular. Let $W_0$ be a complete discrete valuation domain, adically complete for its maximal ideal, with $\mathfrak m_{W_0} = (q)$, together with a surjection $\mathrm{res}_0 : W_0 \to k$ of kernel $\mathfrak m_{W_0}$. Assume $j(E_0) = 0$. Then there exist a Weierstrass curve $\mathcal E$ over $W_0\llbracket t\rrbracket$ with unit discriminant whose reduction along $\mathrm{res}_0 \circ (t \mapsto 0)$ is exactly $E_0$; a commutative formal group $F^u$ over $W_0\llbracket t\rrbracket$ whose power series is the Weierstrass law $\mathcal E$.`formalGroupLawFixed`, and whose image under $\mathrm{res}_0 \circ (t \mapsto 0)$ is the law of $\widehat{E_0}$; such that, writing $\gamma := \operatorname{coeff}_{Z^q}[q]_{F^u} \in W_0\llbracket t\rrbracket$, one has $\operatorname{coeff}_t \gamma - 1 \in \mathfrak m_{W_0}$ and $\gamma - u_1 t \in q\,W_0\llbracket t\rrbracket$ for some unit $u_1$; and there are $a_0 \in W_0$, an integer $e \ge 1$ and a unit $u_2$ with $j(\mathcal E) - a_0 = u_2 t^e$, where $j(\mathcal E)$ is the $j$-invariant `jOfUnit` formed from the unit discriminant.
--
--   This is the case $j(E_0) = 0$ of the construction of a one-parameter Weierstrass deformation over $W_0\llbracket t\rrbracket$ of a supersingular curve whose $j$-invariant moves as a unit times a power of $t$ and whose $q$-division series has linear term a unit times $t$. It is one of three branches, split according to the value of $j(E_0)$ in characteristic $q \ge 5$, used by [`WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le`](thm.html#WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le); here $j(E_0) = 0$ permits the short model $y^2 = x^3 + B$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_zero
    (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (hj0 : E₀.j = 0) :
    ∃ (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
      (_ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
      (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm) (_ : Fu.toPowerSeries = 𝓔.formalGroupLawFixed)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup)
      (_ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀)
      (u₁ : PowerSeries W₀) (_ : IsUnit u₁)
      (_ : PowerSeries.coeff q (Fu.nthSeries q) - u₁ * PowerSeries.X ∈ Ideal.span {(q : PowerSeries W₀)})
      (a₀ : W₀) (e : ℕ) (_ : 1 ≤ e) (u₂ : PowerSeries W₀) (_ : IsUnit u₂),
      𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * PowerSeries.X ^ e := by sorry
