-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_coeff_a
-- name    : SecretaryAdvice.Samples.coeff_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:52.48577+00:00
-- url     : https://prove2.me/theorems/113ea201-de72-4771-8f5b-3abd73f11071
-- title:
--   §5, p. 15 — a(i,s) = P(r_i = n, s_i = s) = 1/(k+1)·∏_{t=1}^{n−1} (s+t)/(k+t+1)
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries, for every round $i$ and every signal $s\in\{0,\dots,k\}$, the probability that the secretary of round $i$ is the best of the $n$ secretaries and has exactly $s$ samples below it is
--   $$a(i,s)=\mathbb P(r_i=n,\,s_i=s)=\frac{1}{k+1}\cdot\prod_{t=1}^{n-1}\frac{s+t}{k+t+1}.$$
--   It does not depend on $i$.
--
--   This is the objective coefficient of the samples LP.
--
--   **Formalization Note** The left side is a count of permutations divided by $(k+n)!$; the right side is the definition `aCoef`. The hypothesis $s\le k$ restricts to the signal space (for $s>k$ the probability is $0$). Rounds are 0-based in Lean; $a$ does not depend on the round.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 15, §5 LP Formulation, formula for a(i, s)

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem coeff_a (n k : ℕ) (i : Fin n) (s : ℕ) (hs : s ≤ k) :
    prob (fun σ : Outcome n k => top σ i ∧ sig σ i = s) = aCoef n k s := by sorry

end SecretaryAdvice.Samples
