-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_greedy_optimal
-- name    : SecretaryAdvice.Samples.greedy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:26.63298+00:00
-- url     : https://prove2.me/theorems/a0e7640e-33f9-4e22-87fe-28b24cbd9b94
-- title:
--   Proof of Theorem 16, p. 17 — the greedy solution (8) is feasible and optimal for the dual of the samples LP
-- statement:
--   For all $n$ and $k$, the greedy solution $u$ of (8) with the samples coefficients ($u(n,s)=a(n,s)$ and $u(i,s)=\max\{0,a(i,s)-\sum_{j>i}\sum_{s'\ge s}u(j,s')c(j,s',i,s)\}$ for $i<n$) is feasible for the dual of the samples LP, and for every dual feasible $u'$,
--   $$\sum_{i=1}^n\sum_{s=0}^k u(i,s)\le\sum_{i=1}^n\sum_{s=0}^k u'(i,s).$$
--
--   This is one of the two hypotheses of Proposition 12; the proof of Theorem 16 establishes it with the perturbation $\Delta$ and Lemma 15.
--
--   **Formalization Note** Feasibility is the remark "It is clear that this leads to a feasible dual solution" (p. 13); optimality is the conclusion of the perturbation argument (p. 17).
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 17, proof sketch of Theorem 16 (and Appendix A, p. 26); eq. (8), p. 13

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem greedy_optimal (n k : ℕ) :
    DualFeasible n k (greedyU n k) ∧
      ∀ u : ℕ → ℕ → ℝ, DualFeasible n k u → dualObj n k (greedyU n k) ≤ dualObj n k u := by sorry

end SecretaryAdvice.Samples
