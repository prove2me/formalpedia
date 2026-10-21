-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_belief_eq_batch
-- name    : SeqDiagnosis.BeliefRecon.belief_eq_batch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:20.174915+00:00
-- url     : https://prove2.me/theorems/9f6fa2ea-f675-4b90-85da-a13618107f5b
-- title:
--   Proof of Theorem 1, p. ec1 — iterated Bayes equals the batch posterior
-- statement:
--   Let $f_i(y)>0$ be a likelihood for every class $i$ and admitted observation $y$, and let $\theta$ be a probability vector. Starting at $\theta$, apply the one-step Bayesian operator to observations $y_1,\ldots,y_t$ in arrival order. The resulting posterior satisfies, for every class $j$,
--
--   $$\Pi_t(y_1,\ldots,y_t,\theta)_j=\frac{\theta_j\prod_{m=1}^t f_j(y_m)}{\sum_{i=0}^N\theta_i\prod_{m=1}^t f_i(y_m)}.$$
--
--   This generic sequential Bayes identity lets the paper's exponential-tilting likelihood product be substituted into the actual iterated posterior. It holds at $t=0$, when the posterior is the prior.
--
--   **Formalization Note** Positivity of every class likelihood is made explicit so every Bayesian denominator is positive. The result is stated independently of the exponential-tilting specialization.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. ec1 (PDF 38), proof of Theorem 1, 'iid. assumption and Bayes’ rule'

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

namespace SeqDiagnosis.BeliefRecon

/-- Repeated one-step Bayes updates equal the normalized likelihood product. -/
theorem belief_eq_batch {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (hf : ∀ i y, 0 < f i y)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1)))
    (ys : List Y) (j : Fin (N + 1)) :
    belief f θ ys j = θ j * (ys.map (f j)).prod /
      ∑ i, θ i * (ys.map (f i)).prod := by sorry

end SeqDiagnosis.BeliefRecon
