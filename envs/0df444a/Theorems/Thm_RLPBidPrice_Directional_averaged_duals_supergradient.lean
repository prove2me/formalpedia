-- Prove2me | Theorems.Thm_RLPBidPrice_Directional_averaged_duals_supergradient
-- name    : RLPBidPrice.Directional.averaged_duals_supergradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T13:12:34.394358+00:00
-- url     : https://prove2.me/theorems/6691d77f-258f-4a5f-aa45-18fc25b0f408
-- title:
--   Proposition 1, p. 212 (formalized as: a fixed measurable dual selection) — (1/N) Σ μ(x, Yᵢ) converges a.s. to a supergradient of E v(x, Y)
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, and $x$ a capacity vector with every component $x^i > 0$. Let $Y$ be a measurable random demand vector on a probability space $(\Omega, P)$ with $Y \ge 0$ almost surely, and let $Y_1, Y_2, \dots$ be measurable random vectors, pairwise independent and each distributed as $Y$. Model a linear programming algorithm that is "initialized with the same data on each run" as a measurable map $f : \mathbb{R}^n \to \mathbb{R}^m$ returning, for every demand vector $y \ge 0$, an optimal vector of dual prices $f(y)$ for $(x, y)$ (a minimizer of $L(x, \cdot)$ over $\mu \ge 0$); write $\mu(x, Y_i) = f(Y_i)$. Then there is a vector $g \in \mathbb{R}^m$ such that almost surely
--   $$\lim_{N \to \infty} \frac{1}{N} \sum_{i=1}^{N} \mu(x, Y_i) = g,$$
--   and $g$ is a supergradient of $J^{PI}(x) = \mathbb{E}\, v(x, Y)$ at $x$:
--   $$J^{PI}(z) \le J^{PI}(x) + g^\top (z - x) \quad \text{for every capacity vector } z \ge 0.$$
--
--   The point of the proposition is the contrast with warm-started algorithms, whose returned duals depend on the history $Y_1, \dots, Y_{i-1}$ and whose averages need not converge.
--
--   **Formalization Note.** "Initialized with the same data on each run (e.g., it is not warm started with data from prior solutions)" is modelled by a fixed function $f$ of the current demand vector; its measurability is an added hypothesis (the paper does not discuss it; a measurable selection of optimal duals exists). "Always exists" is read as almost sure convergence, the strong-law sense in which it holds; the limit $g$ is deterministic. The samples are the paper's "$N$ independent samples of the demand vector" (p. 209); only pairwise independence is assumed. "Subgradient of $Ev_k(x, Y)$" is the supergradient inequality on the feasible capacities $z \ge 0$ ($J^{PI}$ is concave). The time index $k$ is dropped.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 212, Proposition 1

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Directional

/-- Proposition 1, p. 212, formalized as: if the LP algorithm returns the same dual solution
`f y` whenever it is run on the demand `y` (a fixed measurable function of the data), then for
i.i.d. demand samples the running average of the returned dual prices converges almost surely
to a deterministic vector `g`, and `g` is a supergradient of `J^PI` at `x`. -/
theorem averaged_duals_supergradient {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (hA : IsIncidence A) (hr : 0 ≤ r)
    (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) (hfm : Measurable f)
    (hf : ∀ y : Fin n → ℝ, 0 ≤ y → IsDualOpt A r x y (f y))
    (Ys : ℕ → Ω → Fin n → ℝ) (hYsm : ∀ k, Measurable (Ys k))
    (hind : Pairwise fun k l => ProbabilityTheory.IndepFun (Ys k) (Ys l) P)
    (hident : ∀ k, ProbabilityTheory.IdentDistrib (Ys k) Y P P) :
    ∃ g : Fin m → ℝ,
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, f (Ys k ω))
        Filter.atTop (nhds g)) ∧
      ∀ z : Fin m → ℝ, 0 ≤ z → JPI P A r Y z ≤ JPI P A r Y x + g ⬝ᵥ (z - x) := by sorry

end RLPBidPrice.Directional
