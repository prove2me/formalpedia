-- Prove2me | Theorems.Thm_QuadraticRE_lemma_4_9
-- name    : QuadraticRE.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:14:06.308609+00:00
-- url     : https://prove2.me/theorems/1daa66e4-bae1-4475-9de8-9394ebf6e6c1
-- title:
--   Lemma 4.9 — initial values and recurrences (11)–(13)
-- statement:
--   With $p_j$, $q_j(c)$ as in (8) and $\beta(x)=1-(1-x)^2$: $p_0=\tfrac12$, $q_0(0)=0$, $q_0(1)=\tfrac12$, and for every $j\ge0$
--   $$p_{j+1}=2p_j^2-p_j^4,\qquad q_{j+1}(0)=\Bigl(\frac{\beta(q_j(0))+\beta(q_j(1))}{2}\Bigr)^2,\qquad q_{j+1}(1)=\bigl(q_j(0)+q_j(1)-q_j(0)q_j(1)\bigr)^2 .$$
--
--   These recurrences let the probabilities be computed or bounded level by level.
--
--   Differences from the source: none.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma 4.9, p.27

import Mathlib
import Definitions.Def_QuadraticRE_pj

namespace QuadraticRE

/-- Lemma 4.9 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.27: the initial values and the exact recurrences (11)–(13) for the
probabilities defined in (8). -/
theorem lemma_4_9 :
    pj 0 = 1 / 2 ∧ qj 0 0 = 0 ∧ qj 0 1 = 1 / 2 ∧
    ∀ j : ℕ,
      pj (j + 1) = 2 * pj j ^ 2 - pj j ^ 4 ∧
      qj (j + 1) 0 = ((beta (qj j 0) + beta (qj j 1)) / 2) ^ 2 ∧
      qj (j + 1) 1 = (qj j 0 + qj j 1 - qj j 0 * qj j 1) ^ 2 := by sorry

end QuadraticRE
