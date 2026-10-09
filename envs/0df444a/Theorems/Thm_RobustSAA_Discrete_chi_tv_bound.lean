-- Prove2me | Theorems.Thm_RobustSAA_Discrete_chi_tv_bound
-- name    : RobustSAA.Discrete.chi_tv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:02.065718+00:00
-- url     : https://prove2.me/theorems/9db24446-e3a0-4a98-aa1a-17b8a90a26d4
-- title:
--   §10.6, p. 38 — total variation is at most half the Pearson statistic
-- statement:
--   Let $s$ be any finite sample on the known support, let $\widehat p_N$ be its empirical frequencies, and let $F_0$ be any hypothetical distribution with probability vector $p_0$. Pearson's statistic satisfies
--
--   $$
--   d_{\mathrm{TV}}(\widehat p_N,p_0)\leq\frac{X_N(F_0)}{2}.
--   $$
--
--   This is the paper's Cauchy–Schwarz estimate, which turns membership in a Pearson confidence region into a shrinking total-variation bound.
--
--   **Formalization Note** The two sides are compared in $[0,+\infty]$ so that a zero hypothetical probability paired with a positive empirical frequency gives $X_N=+\infty$; no unjustified positive-probability assumption is added.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.6, p. 38, second display

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open MeasureTheory

theorem chi_tv_bound {n N : ℕ} (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) :
    ENNReal.ofReal (dTV (phat s) (pvec F₀)) ≤ chiStat F₀ s / 2 := by sorry

end RobustSAA.Discrete
