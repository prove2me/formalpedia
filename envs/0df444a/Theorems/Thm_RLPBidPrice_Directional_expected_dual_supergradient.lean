-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_expected_dual_supergradient
-- name    : RLPBidPrice.Directional.expected_dual_supergradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:12:09.935268+00:00
-- url     : https://prove2.me/theorems/81775879-1a94-40a3-8980-7df727c9d48d
-- title:
--   §3.1, p. 212 (corrected: ≤ for ≥, z − x for z − y) — E μ(x, Y) is a supergradient of J^PI at x
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, and $x$ a capacity vector with every component $x^i > 0$. Let $Y$ be a random demand vector on a probability space $(\Omega, P)$, measurable and with $Y \ge 0$ almost surely, and let $\mu(\omega)$ be a (strongly) measurable random vector that is, for almost every $\omega$, an optimal vector of dual prices for $(x, Y(\omega))$, i.e. minimizes $L(x, \cdot)$ over $\mu \ge 0$. Then for every capacity vector $z \ge 0$,
--   $$J^{PI}(z) \le J^{PI}(x) + \big(\mathbb{E}\,\mu\big)^\top (z - x), \qquad J^{PI}(x) = \mathbb{E}\, v(x, Y).$$
--   That is, the expected dual price vector is a supergradient of the concave function $J^{PI}$ at $x$ (the paper says "subgradient"). This is the fact behind the RLP estimator in the nondifferentiable case: averaged dual prices estimate a supergradient, not necessarily a gradient.
--
--   **Formalization Note.** The paper's $\mu(x, Y)$ is "the dual solution returned by a given linear programming algorithm"; here it is any measurable selection of optimal dual prices, which is the reading under which $\mathbb{E}\mu(x, Y)$ is defined. $x > 0$ is the paper's implicit setting ("all terms above are uniformly bounded in $Y$": with $x > 0$ every optimal dual price lies in $[0, \max_j r^j]^m$; with a zero capacity the optimal dual prices of that leg are unbounded and $\mathbb{E}\mu$ need not exist). $\mathbb{E}\mu$ is the Bochner integral of the $\mathbb{R}^m$-valued random vector. The time index $k$ is dropped.
--
--   **Correction.** The paper prints $J_k^{PI}(z) \ge J_k^{PI}(x) + E\mu^\top(x, Y)(z - y)$: the inequality sign is reversed (concavity; the one-leg example $r = 1$, $Y = 5$, $x = 1$, $z = 10$ gives $5 \ge 10$) and "$z - y$" is a misprint for "$z - x$".
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 212, §3.1, second display

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- §3.1, p. 212 (sign corrected): for a measurable selection `μ(ω)` of optimal dual prices
at `x > 0`, the expected dual price `E μ` is a supergradient of `J^PI` at `x`. -/
theorem expected_dual_supergradient {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (hA : IsIncidence A) (hr : 0 ≤ r)
    (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (μ : Ω → Fin m → ℝ) (hμm : AEStronglyMeasurable μ P)
    (hμ : ∀ᵐ ω ∂P, IsDualOpt A r x (Y ω) (μ ω))
    (z : Fin m → ℝ) (hz : 0 ≤ z) :
    JPI P A r Y z ≤ JPI P A r Y x + (∫ ω, μ ω ∂P) ⬝ᵥ (z - x) := by sorry

end RLPBidPrice.Directional
