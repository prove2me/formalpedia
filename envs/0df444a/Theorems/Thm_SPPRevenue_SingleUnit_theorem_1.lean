-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_theorem_1
-- name    : SPPRevenue.SingleUnit.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:55.447062+00:00
-- url     : https://prove2.me/theorems/b8b5ce58-cb62-44f1-a9d9-32fa38f2af98
-- title:
--   Theorem 1, p. 13 — in a single-unit n-buyer setting some posted prices p have SPP(p) ≥ 0.6543 · Opt
-- statement:
--   Consider a seller with one item and $n$ buyers with independent private values $v_i \sim \mu_i$. Let $t$ be any single-unit threshold mechanism (measurable thresholds $t_i(v_{-i}) \ge 0$ depending only on the other buyers' values, with almost surely at most one buyer satisfying $v_i \ge t_i$) whose expected revenue $\mathrm{Opt}$ is finite. Then there is a vector of nonnegative prices $p = (p_1,\dots,p_n)$ such that the sequential posted-price mechanism with prices $p$ satisfies
--   $$\mathrm{SPP}(p) \ge 0.6543 \cdot \mathrm{Opt}.$$
--
--   Applied to the thresholds of Myerson's optimal mechanism (Lemma 1, the taxation principle, cited by the paper), this is the paper's Theorem 1: a single deterministic posted-price vector recovers at least $0.6543$ of the optimal revenue, for every number of buyers and all independent value distributions. The proof uses only the threshold form and single-unit feasibility, never optimality, so the statement for arbitrary threshold mechanisms is the same theorem.
--
--   **Formalization Note** Finiteness of $\mathrm{Opt}$ is an added hypothesis and is necessary: there are single-unit threshold mechanisms with infinite expected revenue, while every posted-price revenue is at most $\max_i p_i$. The paper's normalization $\max(\mathrm{MP},\mathrm{UP}) = 1$ assumes it implicitly. The printed "$= \mathrm{Opt}\cdot 1/\mathrm{FR}$" and "$\mathrm{FR} = 1/0.6543$" are not part of the statement (the true value is $1/\mathrm{FR} = 0.65440\ldots \ge 0.6543$); the value of FR is a separate milestone. Revenues are expected values in $[0,\infty]$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 13, Theorem 1

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem theorem_1 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) (hfin : optRev μ t ≠ ⊤) :
    ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧
      ENNReal.ofReal (6543 / 10000) * optRev μ t ≤ sppRev μ p := by sorry

end SPPRevenue.SingleUnit
