-- Prove2me | Theorems.Thm_TsayQF_NoCommit_cc_optimal
-- name    : TsayQF.NoCommit.cc_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:18.797843+00:00
-- url     : https://prove2.me/theorems/426f1d78-9d3d-4ebe-aba3-ad9f54aac878
-- title:
--   §4, p. 1345 — Q*_CC = F^{-1}((p + s − m)/(p + s − u)) is the unique optimal centralized production
-- statement:
--   Consider the supply chain of Tsay (1999) with costs $p > c > m > 0$, $u < m$, $s \ge 0$, demand $X = \mu + \varepsilon$ with $\mu \sim \nu$ independent of $\varepsilon \sim N(0,\sigma_\varepsilon^2)$, and suppose the distribution function $\Theta$ of $\mu$ is differentiable and strictly increasing and $\mu$ has finite variance. Let $F$ be the distribution function of $X$ and
--   $$\Pi_{CC}(Q) = E_X\{p\min[X,Q] - s[X-Q]^+ + u[Q-X]^+\} - mQ$$
--   the expected profit of a central planner producing $Q$ before the demand signal. Then some $Q$ solves
--   $$F(Q) = \frac{p+s-m}{p+s-u},$$
--   and a production $Q$ maximizes $\Pi_{CC}$ over $\mathbb R$ if and only if it solves this equation.
--
--   Since $F$ is strictly increasing, this is the unique centralized optimum $Q^*_{CC} = F^{-1}\big((p+s-m)/(p+s-u)\big)$, the efficiency benchmark against which the decentralized arrangements are measured.
--
--   **Formalization Note** $F^{-1}$ is not a Lean function here: the statement gives existence of a solution and characterizes the maximizers by the equation. Productions range over all of $\mathbb R$; the paper's presumption that demand is almost certainly nonnegative is not needed.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1345, §4

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQF.NoCommit

theorem cc_optimal (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (v : ℝ≥0) :
    (∃ Q : ℝ, cdf (lawX ν v) Q = kS D) ∧
      ∀ Q : ℝ, IsMaxOn (ccProfit D ν v) Set.univ Q ↔ cdf (lawX ν v) Q = kS D := by sorry

end TsayQF.NoCommit
