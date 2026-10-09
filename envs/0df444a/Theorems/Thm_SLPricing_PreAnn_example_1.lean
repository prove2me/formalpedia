-- Prove2me | Theorems.Thm_SLPricing_PreAnn_example_1
-- name    : SLPricing.PreAnn.example_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:57.300632+00:00
-- url     : https://prove2.me/theorems/64dd4aa7-ddf7-455a-86ed-bfd8f5666751
-- title:
--   Example 1, p. 16 — myopic consumers: with social learning the optimal $p_2^*$ exceeds the no-SL price $(p_1+c)/2$
-- statement:
--   Suppose consumers are myopic, $\delta_c=0$, and fix a first-period price $p_1\in(0,1)$.
--
--   1. With social learning ($\gamma>0$), no second-period price $p_2\le (p_1+c)/2$ is optimal: for every such $p_2$ and every purchasing equilibrium $B$ of $\{p_1,p_2\}$ there are a price $p_2'$ and an equilibrium $B'$ of $\{p_1,p_2'\}$ with
--   $$\pi_p(p_1,p_2;B)<\pi_p(p_1,p_2';B').$$
--   2. Without social learning ($\gamma=0$) and if $c<p_1$, the price $(p_1+c)/2$ has an equilibrium and is the unique optimal second-period price: every other $p_2$ earns strictly less, whatever the equilibria.
--
--   Together these say $p_2^*|_{\gamma=k}>p_2^*|_{\gamma\to 0}=(p_1+c)/2$ for every $k>0$: the informational effect of reviews pushes the second-period price up.
--
--   **Formalization Note** The hypothesis $p_1<1$ is added, correcting the page's "arbitrary $p_1>0$": at $p_1\ge 1$ (at most the single type $x=1$ buys early) no reviews are written, the pre-posterior law is the point mass at $0$ even with $\gamma>0$, and $(p_1+c)/2$ is optimal with social learning too, so the claimed strict inequality fails. Part 2 assumes $c<p_1$: for $p_1\le c$ the no-SL optimum is not unique, so the page's $p_2^*|_{\gamma\to0}$ presumes $c<p_1$. Part 1 is claimed for every $p_1\in(0,1)$. The limit $\gamma\to 0$ is the model at $\gamma=0$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Example 1, p. 16; proof, p. 30

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Example 1, p. 16 (proof p. 30): myopic consumers (`δc = 0`), first-period price
`p₁ ∈ (0, 1)` fixed (at `p₁ = 1` nobody buys early, no reviews are written, and `(1 + c)/2` is
optimal with social learning too, so the page's "arbitrary `p₁ > 0`" needs `p₁ < 1`).
With social learning (`γ > 0`) no second-period price `p₂ ≤ (p₁ + c)/2` is optimal:
for each such `p₂` and each of its equilibria some other `p₂'` with an equilibrium earns strictly
more. Without social learning (`γ = 0`) and `c < p₁`, `(p₁ + c)/2` is the unique
optimal second-period price. Together: `p₂*|_{γ=k} > p₂*|_{γ→0}`. -/
theorem example_1 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (hδ : P.δc = 0)
    (p₁ : ℝ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) :
    (∀ p₂ : ℝ, p₂ ≤ (p₁ + P.c) / 2 → ∀ B : Set ℝ, IsPreEq P p₁ p₂ B →
        ∃ (p₂' : ℝ) (B' : Set ℝ), IsPreEq P p₁ p₂' B' ∧
          preProfit P p₁ p₂ B < preProfit P p₁ p₂' B') ∧
      (P.c < p₁ →
        (∃ B : Set ℝ, IsPreEq P.noSL p₁ ((p₁ + P.c) / 2) B) ∧
        ∀ p₂ : ℝ, p₂ ≠ (p₁ + P.c) / 2 → ∀ B B' : Set ℝ, IsPreEq P.noSL p₁ p₂ B →
          IsPreEq P.noSL p₁ ((p₁ + P.c) / 2) B' →
          preProfit P.noSL p₁ p₂ B < preProfit P.noSL p₁ ((p₁ + P.c) / 2) B') := by sorry

end SLPricing.PreAnn
