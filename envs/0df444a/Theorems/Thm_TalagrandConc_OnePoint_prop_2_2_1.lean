-- Prove2me | Theorems.Thm_TalagrandConc_OnePoint_prop_2_2_1
-- name    : TalagrandConc.OnePoint.prop_2_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:58.946992+00:00
-- url     : https://prove2.me/theorems/effcdd7c-cb19-4b8b-b097-7698a6875b63
-- title:
--   Proposition 2.2.1 — $\int e^{tf(A,x)}dP\le a(\alpha,t)^N/P(A)^{\alpha}$
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a probability space, $P=\mu^N$ on $\Omega^N$, $A\subseteq\Omega^N$ measurable with $x\mapsto f(A,x)$ measurable, where $f(A,x)$ is the Hamming distance to $A$. For every $\alpha>0$ and $t\ge0$,
--   $$\int e^{t f(A,x)}\,dP(x)\ \le\ \frac{a(\alpha,t)^N}{P(A)^{\alpha}},\qquad a(\alpha,t)=\frac{\alpha^{\alpha}}{(\alpha+1)^{\alpha+1}}\,\frac{(e^t-e^{-t/\alpha})^{1+\alpha}}{(1-e^{-t/\alpha})(e^t-1)^{\alpha}}.$$
--
--   Replacing $P(A)^{-1}$ by $P(A)^{-\alpha}$ trades a smaller dependence on $P(A)$ against a larger per-coordinate factor; for $\alpha=1$, $a(1,t)$ equals the constant $\tfrac12+\tfrac{e^t+e^{-t}}4$ of Proposition 2.1.1.
--
--   **Formalization Note** Measurability convention as in Proposition 2.1.1. At $t=0$ formula (2.2.2) is $0/0$ and $a(\alpha,0)$ is taken to be its limit $1$. $P(A)^{\alpha}$ is computed in $[0,\infty]$, so $P(A)=0$ gives the right-hand side $+\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 85, Proposition 2.2.1, Eqs. (2.2.1)–(2.2.2)

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem prop_2_2_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
      ≤ ENNReal.ofReal (aAlpha α t) ^ N / (Measure.pi fun _ : Fin N => μ) A ^ α := by sorry

end TalagrandConc.OnePoint
