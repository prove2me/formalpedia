-- Prove2me | Theorems.Thm_RLPBidPrice_Unbiased_gradient_iff_unique_dual
-- name    : RLPBidPrice.Unbiased.gradient_iff_unique_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:47:39.476984+00:00
-- url     : https://prove2.me/theorems/c3162cc2-d99a-4933-8ac7-8e5e8b4eabe7
-- title:
--   §2.1, p. 210 — for x > 0, ∇ₓv(x, Y) exists iff the optimal dual price vector is unique
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, $Y \ge 0$, and let $x$ be a capacity vector with every component $x^i > 0$. Then the perfect-information LP value $x' \mapsto v(x', Y) = \max\{r^\top y : Ay \le x',\ 0 \le y \le Y\}$ is (Fréchet) differentiable at $x$ if and only if the problem
--   $$\min_{\mu \ge 0} L(x, \mu), \qquad L(x, \mu) = \sum_{j=1}^n Y^j (r^j - \mu^\top A^j)^+ + \mu^\top x,$$
--   has exactly one solution, i.e. the optimal vector of dual prices $\mu(x, Y)$ of the capacity constraints $Ay \le x$ is unique.
--
--   This is the reduction of the paper's differentiability question to uniqueness of the dual prices.
--
--   **Formalization Note.** The paper's "$\mu(Y)$" is $\mu(x, Y)$ at the fixed capacity $x$. Differentiability is taken at an interior capacity $x > 0$, where a neighbourhood of $x$ consists of feasible capacities; at a boundary point of $\{x \ge 0\}$ the two-sided derivative is not meaningful. Dual optimality is minimization of the Lagrangian (13) over $\mu \ge 0$ (Eq. (14)). The time index $k$ is dropped.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 210, §2.1, text after Lemma 2 (unnumbered)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

theorem gradient_iff_unique_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    DifferentiableAt ℝ (fun x' => piValue A r x' y₀) x ↔ ∃! μ, IsDualOpt A r x y₀ μ := by sorry

end RLPBidPrice.Unbiased
