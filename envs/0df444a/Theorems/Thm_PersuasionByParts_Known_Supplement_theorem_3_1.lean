-- Prove2me | Theorems.Thm_PersuasionByParts_Known_Supplement_theorem_3_1
-- name    : PersuasionByParts.Known.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:27.856092+00:00
-- url     : https://prove2.me/theorems/bc38d3c0-1a51-4d1c-8269-e6e50bddc3d9
-- title:
--   Theorem 3.1 — Universal guarantee: one product experiment for all decision functions
-- statement:
--   Let $n\ge1$ and let $P=\bigotimes_{i=1}^nP_i$ be any product prior (independent real coordinates with finite means). For a product experiment $\Pi$ and a decision function $g$ (measurable, nondecreasing, $[0,1]$-valued), $V_\Pi(g)=\mathbb E[g(Y_\Pi)]$ with $Y_\Pi$ the sum of the coordinate posterior means, and $V_{\rm joint}(g)$ is the supremum of $\mathbb E[g(Y)]$ over all joint experiments.
--
--   There are absolute constants $c,c'>0$ and, for every $\varepsilon>0$, a constant $c_\varepsilon>0$ depending only on $\varepsilon$, such that for every $n\ge1$ and every product prior $P$ there is a single product experiment $\Pi$, determined by $P$ alone, with the following two properties.
--
--   1. Every decision function $g$ with $q:=V_{\rm joint}(g)>0$ satisfies
--   $$V_\Pi(g)\ \ge\ c\,q^2\exp\!\Big(-c'\,\frac{\ln(e/q)}{\ln\big(e+\ln(e/q)\big)}\Big).$$
--   2. For every $\varepsilon>0$ and every decision function $g$,
--   $$V_\Pi(g)\ \ge\ c_\varepsilon\,V_{\rm joint}(g)^{2+\varepsilon}.$$
--
--   The experiment is chosen before the decision function is known, so one experiment achieves every exponent $2+\varepsilon$ simultaneously. Together with Theorem 4.2, which shows that the sub-polynomial factor cannot be removed for a single product experiment, this is the paper's guarantee for an unknown decision function.
--
--   Differences from the source:
--   - encoding: n ≥ 1 sources (standing assumption of §1.1) → the binder 0 < n; reason: the published model indexes sources by Fin n and keeps positivity as a theorem binder
--   - encoding: absolute constants c, c′ > 0, and for every ε > 0 a constant c_ε > 0 depending only on ε → ∃ c c′ > 0 and ∃ a function cε : ℝ → ℝ with cε ε > 0 for ε > 0, all quantified before n, the prior and the experiment; reason: choosing one c_ε per ε is a function of ε alone; placing the quantifiers first makes the constants uniform over n, P, g and ε
--   - encoding: a product experiment Π determined by P alone → ∃ E : ProductExperiment n after P and before every g and ε; reason: the experiment may depend on the prior only; both bounds hold for the same E
--   - encoding: e, ln, V_joint(g)^{2+ε} → Real.exp 1, Real.log, Real.rpow; reason: the standard functions; V_joint(g) ∈ [0, 1] so rpow is the ordinary power
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 12 / PDF p. 13, Theorem 3.1 (Universal guarantee); model §1.1 and Definition 1.1, printed pp. 1–2 / PDF pp. 2–3

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Supplement

/-- Theorem 3.1, printed p. 12 / PDF p. 13. The absolute constants `c, c'` and the map
`ε ↦ c ε` come first, uniform over `n`, the prior, `g` and `ε`; then for each prior one
product experiment `E` (chosen before `g` and `ε`) satisfies both bounds:
`V_E(g) ≥ c q² exp(-c' ln(e/q) / ln(e + ln(e/q)))` for `q = V_joint(g) > 0`, and
`V_E(g) ≥ c_ε V_joint(g)^(2+ε)` for every `ε > 0` and every `g`. -/
theorem theorem_3_1 :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧
    ∃ cε : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < cε ε) ∧
    ∀ (n : ℕ) (P : Prior n), 0 < n →
      ∃ E : ProductExperiment n,
        (∀ g : Decision, 0 < jointValue P g →
          productPayoff P E g ≥
            c * jointValue P g ^ 2 *
              Real.exp (-c' * (Real.log (Real.exp 1 / jointValue P g) /
                Real.log (Real.exp 1 + Real.log (Real.exp 1 / jointValue P g))))) ∧
        (∀ ε : ℝ, 0 < ε → ∀ g : Decision,
          productPayoff P E g ≥ cε ε * jointValue P g ^ (2 + ε)) := by sorry

end PersuasionByParts.Known.Supplement
