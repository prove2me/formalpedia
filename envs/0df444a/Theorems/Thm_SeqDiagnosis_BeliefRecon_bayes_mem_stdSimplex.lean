-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_bayes_mem_stdSimplex
-- name    : SeqDiagnosis.BeliefRecon.bayes_mem_stdSimplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:19.768998+00:00
-- url     : https://prove2.me/theorems/4607d850-acc7-423e-a8db-e3512b75a6a0
-- title:
--   §2, p. 7 — Bayesian updating preserves the belief simplex
-- statement:
--   Let $f_0,\ldots,f_N$ be class likelihoods that are positive at an admitted observation $y$. If $q$ is a probability vector on classes $0,\ldots,N$, then
--
--   $$0<\sum_{i=0}^N q_i f_i(y),\qquad \mathcal B(q,y)\in S^N.$$
--
--   Thus the one-step Bayesian operator is defined by a positive denominator and returns another belief state. This supplies the domain guarantee needed to iterate the update along an observation list.
--
--   **Formalization Note** Positivity at $y$ makes the denominator nonzero for every prior in the simplex. This §2 statement does not require the exponential-tilting model introduced later in §3.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. 7 (PDF 7), §2, Bayesian operator

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

namespace SeqDiagnosis.BeliefRecon

/-- The one-step Bayesian operator has a positive denominator and preserves beliefs. -/
theorem bayes_mem_stdSimplex {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (y : Y) (hf : ∀ i, 0 < f i y)
    (q : Fin (N + 1) → ℝ) (hq : q ∈ stdSimplex ℝ (Fin (N + 1))) :
    0 < ∑ i, q i * f i y ∧ bayes f q y ∈ stdSimplex ℝ (Fin (N + 1)) := by sorry

end SeqDiagnosis.BeliefRecon
