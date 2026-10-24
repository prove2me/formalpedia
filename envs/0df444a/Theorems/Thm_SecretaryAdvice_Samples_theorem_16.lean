-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_theorem_16
-- name    : SecretaryAdvice.Samples.theorem_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:21.557982+00:00
-- url     : https://prove2.me/theorems/28815066-3c9c-4e2d-8d5b-fc199a4a4a99
-- title:
--   Theorem 16, p. 16 — for every n and k a threshold policy is optimal for secretaries with samples
-- statement:
--   Consider the secretary problem with $k$ samples and $n\ge1$ secretaries: $n+k$ distinct numbers, a uniformly random $k$ of them revealed as samples, the rest arriving in uniformly random order, the goal being to stop at the best of the $n$ arriving numbers. There is a threshold function $t:\{0,1,\dots,k\}\to[n]$ such that the threshold policy
--   $$\tau=\min\{i:\ T_i\text{ and }i\ge t(s_i)\}$$
--   (stop at the first best-so-far secretary $i$ with $i\ge t(s_i)$, where $s_i$ is the number of samples worse than secretary $i$) is optimal: for every policy $q$, randomized and depending on the whole observed relative order,
--   $$\mathrm{win}(q)\le\mathrm{win}(\tau).$$
--
--   Theorem 16 reduces the search for an optimal policy to $k+1$ thresholds, and the greedy dual solution computes them.
--
--   **Formalization Note** $n\ge1$ is needed: for $n=0$ there is nothing to select and $[n]$ is empty. Competitors are all policies whose stopping probabilities lie in $[0,1]$ and depend only on the information (the relative order of the samples and the secretaries seen so far), not on the outcome. Rounds are 0-based in Lean.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 16, Theorem 16

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting

namespace SecretaryAdvice.Samples

theorem theorem_16 (n k : ℕ) (hn : 1 ≤ n) :
    ∃ t : ℕ → ℕ, ValidThreshold n k t ∧
      ∀ q : Policy n k, ValidPolicy q → win q ≤ win (thresholdPolicy (n := n) (k := k) t) := by sorry

end SecretaryAdvice.Samples
