-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_claim_ii
-- name    : SecretaryAdvice.Samples.claim_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:14.512078+00:00
-- url     : https://prove2.me/theorems/d54769fe-7a26-4da8-96c8-cef4ef358467
-- title:
--   Proof of Theorem 16, claim (ii), p. 16 — R_i = −δ·(i−1)/(i*−1) ≤ 0 for 1 ≤ i ≤ i*
-- statement:
--   Fix $k$, a signal $s^*\in\{0,\dots,k\}$, an index $i^*\ge 2$ and $\delta\ge 0$, let $\Delta$ be the perturbation of the proof of Theorem 16 and
--   $$R_i=\sum_{j\ge i}\sum_{s\le s^*}\Delta(j,s)$$
--   the cumulative change of the dual objective. Then for every $1\le i\le i^*$,
--   $$R_i=-\delta\cdot\frac{i-1}{i^*-1}\le 0.$$
--
--   In particular $R_1=0\le 0$: the perturbation does not increase the dual objective, which is the step that shows the greedy solution optimal.
--
--   **Formalization Note** $i^*\ge2$ is needed for the fraction $(i-1)/(i^*-1)$ to be the paper's (for $i^*=1$ it would divide by $0$). $\delta\ge 0$ is needed for "$\le 0$"; in the proof $\delta\ge 0$ because $u$ is dual feasible. The sum over $j\ge i$ is taken up to $i^*$, beyond which $\Delta$ vanishes.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 16, proof sketch of Theorem 16, claim (ii); full proof in Appendix A, p. 26

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem claim_ii (k istar sstar : ℕ) (δ : ℝ) (hsstar : sstar ≤ k) (histar : 2 ≤ istar)
    (hδ : 0 ≤ δ) (i : ℕ) (hi : 1 ≤ i) (hii : i ≤ istar) :
    cumChange k istar sstar δ i = -δ * (((i : ℝ) - 1) / ((istar : ℝ) - 1)) ∧
      cumChange k istar sstar δ i ≤ 0 := by sorry

end SecretaryAdvice.Samples
