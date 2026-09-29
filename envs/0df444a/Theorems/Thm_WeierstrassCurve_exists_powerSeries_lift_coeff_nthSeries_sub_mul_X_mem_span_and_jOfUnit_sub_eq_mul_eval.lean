-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval
-- name    : WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/5502b98f-91e6-5f79-be9c-dadff623a323
-- title:
--   Universal Weierstrass lift of a supersingular curve over W₀[[t]]
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$ and $E_0$ a Weierstrass curve over $k$ which is elliptic and whose formal group $F_{E_0}$ (the formal group whose defining power series is `formalGroupLawFixed`) satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with the ideal taken to be $\bot$ there is a unit $u$ of $k\llbracket X\rrbracket$ with $[q]_{F_{E_0}} = u \cdot$ `drinfeldDivisor` $q\,0\,0$, where $[q]$ denotes the $q$-th iterate `nthSeries q` obtained by repeatedly substituting the previous iterate and $X$ into the group law. Let $W_0$ be a complete discrete valuation domain, adically complete for its maximal ideal, with $\mathfrak m_{W_0} = (q)$, and let $\mathrm{res}_0 : W_0 \to k$ be a surjective ring homomorphism with kernel $\mathfrak m_{W_0}$. Then there exist: a Weierstrass curve $\mathcal E$ over $W_0\llbracket t\rrbracket$ with $\Delta_{\mathcal E}$ a unit, whose base change along $\mathrm{res}_0 \circ \mathrm{constantCoeff}$ is $E_0$; a commutative formal group $F_u$ over $W_0\llbracket t\rrbracket$ whose power series is $\mathcal E$'s `formalGroupLawFixed` and whose base change along $\mathrm{res}_0 \circ \mathrm{constantCoeff}$ is $F_{E_0}$, such that, writing $\gamma \in W_0\llbracket t\rrbracket$ for the coefficient of $X^q$ in $[q]_{F_u}$, one has $\mathrm{coeff}_t(\gamma) - 1 \in \mathfrak m_{W_0}$ and $\gamma - u_1 t \in (q)$ for some unit $u_1$ of $W_0\llbracket t\rrbracket$; and $a_0 \in W_0$, an integer $e \ge 1$, a unit $u_2$ of $W_0\llbracket t\rrbracket$ and a monic $P \in W_0[X]$ of degree $e$ with $P_i \in \mathfrak m_{W_0}^{\lfloor (e-i)q/(q+1)\rfloor + 1}$ for all $i < e$, such that $j(\mathcal E) - a_0 = u_2 \cdot P(t)$, the $j$-invariant being `jOfUnit` computed from the unit discriminant.
--
--   This is the explicit universal deformation of a supersingular elliptic curve over a complete discrete valuation ring with uniformiser $q$: the Hasse parameter $t$ appears linearly in the $X^q$-coefficient of multiplication by $q$ on the formal group, and $j - a_0$ is a unit times a distinguished Weierstrass polynomial whose roots lie deeper than the Drinfeld depth $q/(q+1)$. It is the prime-independent form of the statement, used in the construction of the rigid data attached to level structures on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval.lean

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

theorem WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) :
    ∃ (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
      (_ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
      (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm) (_ : Fu.toPowerSeries = 𝓔.formalGroupLawFixed)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup)
      (_ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀)
      (u₁ : PowerSeries W₀) (_ : IsUnit u₁)
      (_ : PowerSeries.coeff q (Fu.nthSeries q) - u₁ * PowerSeries.X ∈ Ideal.span {(q : PowerSeries W₀)})
      (a₀ : W₀) (e : ℕ) (_ : 1 ≤ e) (u₂ : PowerSeries W₀) (_ : IsUnit u₂)

      (P : Polynomial W₀) (_ : P.Monic) (_ : P.natDegree = e)
      (_ : ∀ i < e, P.coeff i ∈ maximalIdeal W₀ ^ ((e - i) * q / (q + 1) + 1)),
      𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ =
        u₂ * (P.map (algebraMap W₀ (PowerSeries W₀))).eval PowerSeries.X := by sorry
