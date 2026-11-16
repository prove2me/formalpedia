-- Prove2me | Theorems.Thm_PersuasionByParts_Known_Supplement_theorem_4_1
-- name    : PersuasionByParts.Known.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:53.260035+00:00
-- url     : https://prove2.me/theorems/cb71fe14-f906-4b1e-b9be-c0f3a0ac7cc9
-- title:
--   Theorem 4.1 — Two-source quadratic lower bound: $V_{\rm joint}(t)\ge q$, $V_{\rm prod}(t)\le(q+\delta)^2$
-- statement:
--   For every $q\in(0,1)$ and every $\delta\in(0,1)$ there exist a two-source product prior $P=P_1\otimes P_2$ (independent real coordinates with finite means) and a cutoff $t\in\mathbb R$ such that
--
--   $$V_{\rm joint}(t)\ \ge\ q\qquad\text{and}\qquad V_{\rm prod}(t)\ \le\ (q+\delta)^2 .$$
--
--   Here $V_{\rm joint}(t)$ is the largest achievable probability that the posterior mean of $X_1+X_2$ is at least $t$ under a joint experiment, and $V_{\rm prod}(t)$ the supremum of the probability that the sum of the coordinate posterior means is at least $t$ over all product experiments. The theorem shows that the quadratic guarantee $V_{\rm prod}(t)\ge\frac1{36}V_{\rm joint}(t)^2$ of the mission's goal is tight up to the constant factor, already for two sources and one known cutoff.
--
--   Differences from the source:
--   - encoding: a two-source product prior P = P_1 ⊗ P_2 → P : Prior 2 of the published model (two real marginals with finite means, product law); reason: the paper's priors have finite means (§1.1); requiring this of the witness only makes the existential claim stronger, and the proof's priors are finitely supported
--   - encoding: V_joint(t), V_prod(t) → jointCutoff P t and productCutoff P t (suprema over all joint, resp. all product experiments); reason: the published model's definitions of these values
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 16 / PDF p. 17, Theorem 4.1 (Two-source quadratic lower bound)

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Supplement

/-- Theorem 4.1, printed p. 16 / PDF p. 17: for every `q, δ ∈ (0, 1)` some two-source
product prior and some real cutoff `t` have `V_joint(t) ≥ q` and `V_prod(t) ≤ (q + δ)²`,
where `V_prod` is the supremum over all product experiments. -/
theorem theorem_4_1 (q δ : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ (P : Prior 2) (t : ℝ), jointCutoff P t ≥ q ∧ productCutoff P t ≤ (q + δ) ^ 2 := by sorry

end PersuasionByParts.Known.Supplement
