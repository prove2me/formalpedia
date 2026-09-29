-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries
-- name    : WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/3e7436bc-1431-574e-8611-f5570e9b455c
-- title:
--   Commutative lift over W₀llbracket trrbracket with unit first-order q-series coefficient
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$ and $E_0$ an elliptic Weierstrass curve over $k$, and assume that the formal group $\widehat{E_0}$ (the formal group whose law is [`WeierstrassCurve.formalGroupLawFixed`](def/WeierstrassCurve_FormalGroupLaw.html#L638), obtained by substituting `fgZ3Fixed` into `fgInv`) satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with the ideal of $k$ taken to be $\bot$ there is a unit $u \in k\llbracket Z\rrbracket$ with $\widehat{E_0}.\mathrm{nthSeries}\,q = u \cdot \widehat{E_0}.\mathrm{drinfeldDivisor}\,q\,0\,0$, where $\mathrm{nthSeries}$ is the multiplication-by-$n$ series defined recursively by $\mathrm{nthSeries}\,0 = 0$ and $\mathrm{nthSeries}(n+1) = F(\mathrm{nthSeries}\,n, Z)$. Let $W_0$ be a discrete valuation domain, complete for its maximal-ideal-adic topology, with $\mathfrak m_{W_0} = (q)$, and let $\mathrm{res}_0 : W_0 \to k$ be a surjective ring homomorphism with kernel $\mathfrak m_{W_0}$. Then there exists a formal group $F^u$ over $W_0\llbracket t\rrbracket$ satisfying the predicate `FormalGroup.IsComm`, such that $F^u$ base changes to $\widehat{E_0}$ along $f \mapsto \mathrm{res}_0(f(0))$ — that is, the law of $\widehat{E_0}$ is the coefficientwise image of the law of $F^u$ under that homomorphism — and such that the coefficient of $t$ in the coefficient of $Z^q$ in $F^u.\mathrm{nthSeries}\,q$ is congruent to $1$ modulo $\mathfrak m_{W_0}$.
--
--   This is the lifting step behind the Igusa-type statement that the Hasse invariant of the universal deformation of a height-two (supersingular) formal group has a simple zero: the formal group of a suitable Weierstrass deformation of $E_0$ over $W_0\llbracket t\rrbracket$ has normalised first-order $q$-series coefficient. It feeds the analysis of Drinfeld bases and of the completed local rings of modular curves of full level, being cited by the `ModularCurve.FullLevel.Diamond` results on domains, integral closedness and reducedness of those completions, and by the existence statement for Drinfeld bases with regular Hasse parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries.lean

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

theorem WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) :
    ∃ (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup),
      PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀ := by sorry
