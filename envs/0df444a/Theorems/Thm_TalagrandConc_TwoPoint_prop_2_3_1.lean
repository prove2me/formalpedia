-- Prove2me | Theorems.Thm_TalagrandConc_TwoPoint_prop_2_3_1
-- name    : TalagrandConc.TwoPoint.prop_2_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:55.013225+00:00
-- url     : https://prove2.me/theorems/19358d08-0e29-48c8-a1cd-7b1f6ffce496
-- title:
--   Proposition 2.3.1 — $\int e^{t f(A,x)}\,dP \le b(\alpha,t,p)^N/P(A)^\alpha$ on $\{0,1\}^N$
-- statement:
--   Let $\Omega=\{0,1\}$, let $\mu$ be the probability with $\mu(\{1\})=p\in[0,1]$, and let $P=\mu^N$ on $\Omega^N$. For $A\subseteq\Omega^N$ let $f(A,x)$ be the Hamming distance from $x$ to $A$, the least number of coordinates in which $x$ differs from a point of $A$. Let $b(\alpha,t,p)$ be the constant of Eqs. (2.3.2)–(2.3.3):
--   $$b(\alpha,t,p)=((1-p)e^{t}+p)(p+(1-p)e^{-t/\alpha})^{\alpha}\ \ (p\ge 1/2),\qquad b(\alpha,t,p)=((1-p)e^{-t}+p)(p+(1-p)e^{t/\alpha})^{\alpha}\ \ (p\le 1/2).$$
--
--   Then for every $N\ge 0$, every $A\subseteq\Omega^N$, every $t\ge 0$ and every $\alpha\ge 1$,
--   $$\int e^{t f(A,x)}\,dP(x)\le\frac{b(\alpha,t,p)^N}{P(A)^{\alpha}}.$$
--
--   The factor $b(\alpha,t,p)$ takes the bias $p$ of the coordinates into account. For small $t$ it is close to $\exp(p(1-p)(1+1/\alpha)t^2/2)$, which is smaller than the bias-free factor of the general case when $p$ is close to $0$ or $1$. Applied to $A=\{x:\sum_i x_i\le k\}$ it gives tail bounds for the binomial law.
--
--   **Formalization Note** The right-hand side is computed in $[0,\infty]$, so $P(A)=0$ gives $+\infty$, and $f(\emptyset,x)=+\infty$. The hypothesis $\alpha\ge 1$ is the page's.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 87, Proposition 2.3.1, Eqs. (2.3.1)–(2.3.3)

import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Proposition 2.3.1, Eqs. (2.3.1)–(2.3.3), p. 87. `Ω = {0,1}`,
`P = μ^N` with `μ({1}) = p`, `f` the Hamming distance (2.1.1). For every `A ⊆ Ω^N`,
`t ≥ 0`, `α ≥ 1`: `∫ e^{t f(A,x)} dP(x) ≤ b(α, t, p)^N / P(A)^α`. -/
theorem prop_2_3_1 (p : unitInterval) (N : ℕ) (A : Set (Fin N → Bool))
    (α : ℝ) (hα : 1 ≤ α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, TalagrandConc.OnePoint.expMul t (hammingDistToSet A x) ∂(productMeasure N p))
      ≤ ENNReal.ofReal (bConst α t (p : ℝ)) ^ N / (productMeasure N p A) ^ α := by sorry

end TalagrandConc.TwoPoint
