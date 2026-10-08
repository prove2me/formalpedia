-- Prove2me | Theorems.Thm_TalagrandConc_TwoPoint_thm_2_3_4
-- name    : TalagrandConc.TwoPoint.thm_2_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:58.681987+00:00
-- url     : https://prove2.me/theorems/f4a6d048-b739-4681-8fed-ad8ddf58a7fb
-- title:
--   Theorem 2.3.4 — $\int e^{t f(A,x)}\,dP(x) \le a(\alpha,t)^N/P_1(A)^\alpha$ for the one-sided distance
-- statement:
--   Let $\Omega=\{0,1\}$ and let $\mu,\mu_1$ be two probabilities on $\Omega$ with $p=\mu(\{1\})$ and $p_1=\mu_1(\{1\})>p$. Let $P=\mu^N$ and $P_1=\mu_1^N$ be the product probabilities on $\Omega^N$. For $A\subseteq\Omega^N$ and $x\in\Omega^N$ consider the one-sided distance
--   $$f(A,x)=\min\big\{\operatorname{card}\{i\le N:\ x_i=1,\ y_i=0\}\ :\ y\in A\big\},$$
--   and for $\alpha>0$, $t\ge 0$ set
--   $$a(\alpha,t)=\max\Big(1,\ (1-p+pe^{t})\,(p_1e^{-t/\alpha}+1-p_1)^{\alpha}\Big).$$
--
--   Then for every $N\ge 0$ and every $A\subseteq\Omega^N$,
--   $$\int e^{t f(A,x)}\,dP(x)\le\frac{a(\alpha,t)^N}{P_1(A)^{\alpha}}.$$
--
--   The exponential moment is taken under $P$, while the size of $A$ is measured under the second product measure $P_1$, which puts more weight on the value $1$. For small $t$ one has $a(\alpha,t)=1$, and then the bound does not depend on $N$; for $\alpha=1$ this happens whenever $e^{t}\le p_1(1-p)/(p(1-p_1))$, and gives
--   $$\int\Big(\frac{p_1(1-p)}{p(1-p_1)}\Big)^{f(A,x)}dP(x)\le\frac{1}{P_1(A)}.$$
--
--   **Formalization Note** $\Omega$ is `Bool` with $1$ = `true`; the integral is a lower Lebesgue integral in $[0,\infty]$ and every subset of $\{0,1\}^N$ is measurable. $f(\emptyset,x)=+\infty$, and $P_1(A)=0$ makes the right-hand side $+\infty$. The range $\alpha>0$ is read from Section 2.2, where the exponent $\alpha$ of $P(A)$ was introduced; the theorem's page does not restate it.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 90, Theorem 2.3.4, Eq. (2.3.6)

import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Theorem 2.3.4, Eq. (2.3.6), p. 90. `Ω = {0,1}`, `P = μ^N` with
`μ({1}) = p`, and `P₁ = μ₁^N` with `μ₁({1}) = p₁ > p`. For every `A ⊆ Ω^N`, `α > 0`
(the range of §2.2; the page does not restate it) and `t ≥ 0`,
`∫ e^{t f(A,x)} dP(x) ≤ a(α, t)^N / P₁(A)^α` for the one-sided distance `f`. -/
theorem thm_2_3_4 (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (N : ℕ) (A : Set (Fin N → Bool)) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, TalagrandConc.OnePoint.expMul t (oneSidedDistToSet A x) ∂(productMeasure N p))
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ)) ^ N / (productMeasure N p₁ A) ^ α := by sorry

end TalagrandConc.TwoPoint
