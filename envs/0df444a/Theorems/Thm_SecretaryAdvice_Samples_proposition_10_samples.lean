-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_proposition_10_samples
-- name    : SecretaryAdvice.Samples.proposition_10_samples
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:56.067616+00:00
-- url     : https://prove2.me/theorems/624f419e-768f-4e62-8b85-5027f101df5c
-- title:
--   Proposition 10, p. 10, for samples — every feasible z is achieved by a policy; threshold-shaped z by the threshold policy
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries:
--
--   1. For every $z$ feasible for the samples primal LP there is a valid policy $q$ with $\mathrm{win}(q)=\sum_i\sum_s z(i,s)\,a(i,s)$.
--   2. If $t:\mathcal S\to[n]$ is a threshold function and $z$ is feasible and has the threshold shape for $t$ ($z(i,s)=0$ for $i<t(s)$, the $(i,s)$-constraint tight for $i\ge t(s)$), then the threshold policy for $t$ achieves it:
--   $$\mathrm{win}(\text{threshold policy } t)=\sum_i\sum_s z(i,s)\,a(i,s).$$
--
--   Part 1 is Proposition 10 specialized to Example 4. Part 2 is the observation in the proof of Proposition 12 that, for a threshold-shaped solution, the reconstructed policy (6) stops with probability $0$ before $t(s)$ and with probability $1$ from $t(s)$ on.
--
--   **Formalization Note** Part 2 is an addition to the printed Proposition 10, recorded here because Theorem 16 needs the policy to be the threshold policy itself.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 10, Proposition 10, and p. 13, proof of Proposition 12, Step 1 (with the samples coefficients of p. 15)

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem proposition_10_samples (n k : ℕ) :
    (∀ z : ℕ → ℕ → ℝ, PrimalFeasible n k z →
      ∃ q : Policy n k, ValidPolicy q ∧ win q = primalObj n k z) ∧
    (∀ (t : ℕ → ℕ) (z : ℕ → ℕ → ℝ), ValidThreshold n k t → PrimalFeasible n k z →
      ThresholdShaped n k t z → win (thresholdPolicy (n := n) (k := k) t) = primalObj n k z) := by sorry

end SecretaryAdvice.Samples
