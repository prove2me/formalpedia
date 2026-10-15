-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_proposition_9_samples
-- name    : SecretaryAdvice.Samples.proposition_9_samples
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:05.608562+00:00
-- url     : https://prove2.me/theorems/add75a27-c635-41af-a1ab-789a88b07c75
-- title:
--   Proposition 9, p. 10, for samples — every best-so-far policy yields a feasible z with objective equal to its winning probability
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries, let $q$ be a policy that stops only in rounds where the current secretary is the best so far. Then there is $z:[n]\times\mathcal S\to\mathbb R$ feasible for the samples primal LP,
--   $$z(i,s)\ge 0,\qquad z(i,s)\le 1-\sum_{j<i}\sum_{s'\le s}z(j,s')\,c(i,s,j,s'),$$
--   such that
--   $$\sum_{i}\sum_{s}z(i,s)\,a(i,s)=\mathrm{win}(q).$$
--
--   This is Proposition 9 specialized to Example 4, whose signal structure satisfies NF and HI. With the next item it identifies the LP value with the optimal winning probability.
--
--   **Formalization Note** The hypothesis that $q$ stops only on best-so-far rounds is the one the derivation of (4) uses ("Since each $j<i$ is only picked in the event $T_j$", p. 10); `best_so_far_reduction` shows it costs nothing. The LP is the printed samples LP with the explicit coefficients $a$ and $c$, not the abstract one with probabilities.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 10, Proposition 9 (with the samples coefficients of p. 15)

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem proposition_9_samples (n k : ℕ) (q : Policy n k) (hq : ValidPolicy q)
    (hbsf : ∀ (i : Fin n) (x : Info k i.val), infoBestSoFar x = false → q i x = 0) :
    ∃ z : ℕ → ℕ → ℝ, PrimalFeasible n k z ∧ primalObj n k z = win q := by sorry

end SecretaryAdvice.Samples
