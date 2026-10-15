-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_greedy_monotone
-- name    : SecretaryAdvice.Samples.greedy_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:23.466277+00:00
-- url     : https://prove2.me/theorems/e4d41102-73ef-40b2-bc74-e8d7b9cb5cda
-- title:
--   Proof of Theorem 16, p. 16 — the greedy dual solution u(i,s) of the samples LP is non-decreasing in i
-- statement:
--   For all $n$, $k$ and every signal $s\in\{0,\dots,k\}$, the greedy dual solution $u$ of (8) with the samples coefficients satisfies
--   $$u(i,s)\le u(i+1,s)\qquad(1\le i<n).$$
--
--   This is the second hypothesis of Proposition 12. The paper derives it from $a(i,s)$ not depending on $i$ and $c(j,s',i,s)$ being non-increasing in $i$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 16, proof sketch of Theorem 16 (monotonicity); Appendix A, p. 25

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem greedy_monotone (n k s : ℕ) (hs : s ≤ k) (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    greedyU n k i s ≤ greedyU n k (i + 1) s := by sorry

end SecretaryAdvice.Samples
