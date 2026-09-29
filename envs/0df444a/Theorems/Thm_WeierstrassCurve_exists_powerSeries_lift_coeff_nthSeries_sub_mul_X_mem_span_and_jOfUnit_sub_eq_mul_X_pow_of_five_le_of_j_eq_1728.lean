-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_1728
-- name    : WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/f7bd6737-04a0-5978-995d-5a92932e1498
-- title:
--   Monomial j universal deformation at a supersingular point, case j=1728
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $k$ be a field of characteristic $q$ and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`: for the ideal $\bot$ there is a unit power series $u$ with $[q]$-series $\mathrm{nthSeries}\,q$ of $\widehat{E_0}$ equal to $u\cdot\mathrm{drinfeldDivisor}\,q\,0\,0$ (equivalently, by the cited criterion, to $u\,X^{q^2}$), and suppose $j(E_0)=1728$. Let $W_0$ be a complete (adically complete for its maximal ideal) discrete valuation domain with $\mathfrak m_{W_0}=(q)$, and $\mathrm{res}_0:W_0\to k$ a surjective ring homomorphism with kernel $\mathfrak m_{W_0}$. Then there exist a Weierstrass curve $\mathcal E$ over $W_0[[X]]$ with $\Delta_{\mathcal E}$ a unit whose coefficientwise image under $\mathrm{res}_0\circ\mathrm{constantCoeff}$ is $E_0$; a formal group $F^u$ over $W_0[[X]]$ which is commutative, whose underlying two‑variable series is the Weierstrass law $\mathcal E.\mathrm{formalGroupLawFixed}$, and which base‑changes along $\mathrm{res}_0\circ\mathrm{constantCoeff}$ to $\widehat{E_0}$ (i.e. $\widehat{E_0}$'s series is the image of $F^u$'s); with $\gamma:=\mathrm{coeff}_q(\mathrm{nthSeries}\,q\,F^u)\in W_0[[X]]$, one has $\mathrm{coeff}_1\gamma-1\in\mathfrak m_{W_0}$ and $\gamma-u_1X\in q\,W_0[[X]]$ for some unit $u_1$; and there are $a_0\in W_0$, $e\ge 1$ and a unit $u_2$ with $j(\mathcal E)-a_0=u_2X^{e}$.
--
--   This is the $j(E_0)=1728$ case of the construction of a one‑parameter Weierstrass deformation over $W_0[[X]]$ of a supersingular curve in characteristic $q\ge 5$, for which the $j$-invariant differs from a constant by a unit times a power of the deformation parameter and the $q$-series has the expected linear leading behaviour. It is one of the three cases, split according to the value of $j(E_0)$, feeding the general statement [`WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le`](thm.html#WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_1728.lean

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

theorem WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_1728
    (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (hj1728 : E₀.j = 1728) :
    ∃ (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
      (_ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
      (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm) (_ : Fu.toPowerSeries = 𝓔.formalGroupLawFixed)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup)
      (_ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀)
      (u₁ : PowerSeries W₀) (_ : IsUnit u₁)
      (_ : PowerSeries.coeff q (Fu.nthSeries q) - u₁ * PowerSeries.X ∈ Ideal.span {(q : PowerSeries W₀)})
      (a₀ : W₀) (e : ℕ) (_ : 1 ≤ e) (u₂ : PowerSeries W₀) (_ : IsUnit u₂),
      𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * PowerSeries.X ^ e := by sorry
