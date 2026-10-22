-- Prove2me | Theorems.Thm_RLPBidPrice_Unbiased_theorem1_unbiased_gradient
-- name    : RLPBidPrice.Unbiased.theorem1_unbiased_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:48:58.741759+00:00
-- url     : https://prove2.me/theorems/9b8c4d44-6745-4e1b-80a3-839906089695
-- title:
--   Theorem 1 (corrected: C1 on [A I], independent demands) — ∇ₓE v(x, Y) = E ∇ₓv(x, Y) = E μ(x, Y)
-- statement:
--   Let $A$ be an $m \times n$ 0/1 leg–itinerary incidence matrix with nonzero columns, $r \ge 0$ the fares, and $x \ge 0$ a capacity vector satisfying Condition C1′ (whenever $x$ lies in the span of a set of columns of $[A\ I]$, that set spans $\mathbb{R}^m$). Let $Y = (Y^1, \dots, Y^n)$ be a random demand vector on a probability space $(\Omega, P)$: measurable, $Y \ge 0$ almost surely, with mutually independent components satisfying Condition 2 ($t \mapsto P(Y^j \le t)$ continuous for every $j$). Let $v(x, Y) = \max\{r^\top y : Ay \le x,\ 0 \le y \le Y\}$ and $J^{PI}(x) = \mathbb{E}\, v(x, Y)$. Then:
--
--   1. $x' \mapsto v(x', Y)$ is differentiable at $x$ almost surely;
--   2. $J^{PI}$ is differentiable at $x$ and $\nabla_x \mathbb{E}\, v(x, Y) = \mathbb{E}\, \nabla_x v(x, Y)$ (the derivative of $J^{PI}$ at $x$ is the expectation of the pathwise derivatives);
--   3. for every random vector $\mu(x, Y)$ that is (almost everywhere strongly) measurable and almost surely an optimal dual price vector for the capacity constraints (a minimizer of $L(x, \cdot)$ over $\mu \ge 0$, Eq. (14)), $J^{PI}$ has gradient $\mathbb{E}\, \mu(x, Y)$ at $x$:
--   $$\nabla_x \mathbb{E}\, v(x, Y) = \mathbb{E}\, \nabla_x v(x, Y) = \mathbb{E}\, \mu(x, Y).$$
--
--   This is the paper's main result: the randomized linear programming estimate $\frac{1}{N}\sum_{i=1}^N \mu(x, Y_i)$ of the bid prices is an unbiased estimator of the gradient of the expected perfect-information revenue.
--
--   **Formalization Note.** The time index $k$ is dropped. Gradients are Fréchet derivatives on $\mathbb{R}^m$ (with its sup norm; differentiability does not depend on the norm); in part 3 the derivative is the functional $h \mapsto \sum_i (\mathbb{E}\,\mu^i)\, h^i$, i.e. the gradient is the vector of expected dual prices. Part 2 needs no dual selection; part 3 quantifies over measurable selections, because the expectation of a non-measurable selection is not defined. No integrability hypothesis on $Y$ is made: $0 \le v(x, Y) \le \bar r \sum_i x^i$.
--
--   **Correction.** The printed theorem assumes Condition 1 and Condition 2 only and is false. (i) Condition 1 is applied to the columns of $[A\ I]$ (C1′): with $A$ having rows $(0,1,1), (1,1,0), (1,0,1)$, $r = (100,1,1)$, $x = (1,1,1)$ and $Y^j$ i.i.d. uniform on $[0,2]$, Conditions 1 and 2 hold but $\mathbb{E}\, v(\cdot, Y)$ has one-sided slopes of about $0.74$ and $50.5$ in the second coordinate at $x$. (ii) The components of $Y$ are mutually independent: with one leg, $x = 1$, fares $(2,1)$ and $Y^2 = 1 - Y^1$, $Y^1$ uniform on $[0,1]$, the LP is degenerate almost surely and $J^{PI}$ has a kink at $x$.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 211, Theorem 1

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

theorem theorem1_unbiased_gradient {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (hC1 : ConditionOnePrime A x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hC2 : ConditionTwo P Y) (hind : ProbabilityTheory.iIndepFun (fun j ω => Y ω j) P) :
    (∀ᵐ ω ∂P, DifferentiableAt ℝ (fun x' => piValue A r x' (Y ω)) x) ∧
    HasFDerivAt (JPI P A r Y) (∫ ω, fderiv ℝ (fun x' => piValue A r x' (Y ω)) x ∂P) x ∧
    (∀ μ : Ω → Fin m → ℝ, AEStronglyMeasurable μ P →
      (∀ᵐ ω ∂P, IsDualOpt A r x (Y ω) (μ ω)) →
      HasFDerivAt (JPI P A r Y) (gradCLM (fun i => ∫ ω, μ ω i ∂P)) x) := by sorry

end RLPBidPrice.Unbiased
