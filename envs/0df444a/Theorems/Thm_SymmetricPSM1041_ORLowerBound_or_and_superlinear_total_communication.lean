-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_or_and_superlinear_total_communication
-- name    : SymmetricPSM1041.ORLowerBound.or_and_superlinear_total_communication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:36.8356+00:00
-- url     : https://prove2.me/theorems/8359e63c-ed05-493f-b59d-072b0c23c6f5
-- title:
--   Theorem 1 — superlinear total communication for OR and AND
-- statement:
--   For every real $A>0$, there is a positive integer $N$, fixed independently of the protocol, such that for every $n\ge N$, for either $f=\mathrm{OR}_n$ or $f=\mathrm{AND}_n$, and for every perfectly correct, support-private PSM protocol $P$ for $f$, there are an input $x$ and a shared seed $r$ with
--
--   $$\sum_{i\in[n]}|M_i(x_i,r)|\ge A n.$$
--
--   The same threshold serves both functions and every finite nonempty shared-randomness size, every local alphabet and every decoder. This is the complete operational statement $C(\mathrm{OR}_n)=\omega(n)$ and $C(\mathrm{AND}_n)=\omega(n)$, with arbitrary variable-length binary messages. It asserts a bound for all sufficiently large $n$, not merely infinitely many sizes. No effective rate for $N(A)$ is claimed.
--
--   The result gives a superlinear lower bound even under support privacy, and therefore also for protocols meeting perfect privacy. The asymptotic bound applies to worst-case actual total length, separately from sums of logarithmic alphabet sizes.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: C(OR)=ω(n), with the same bound for AND → for each A>0 one N works for both functions, all n≥N and all admissible protocols, with an actual transcript of length at least A n; reason: this is the uniform little-omega assertion; the larger of two thresholds serves OR and AND
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 3, Theorem 1; p. 16, Corollary 20 and pp. 15–16 derivation

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

namespace SymmetricPSM1041.ORLowerBound

theorem or_and_superlinear_total_communication :
    ∀ A : ℝ, 0 < A → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ f : (Fin n → Bool) → Bool, (f = orFunction ∨ f = andFunction) →
      ∀ P : PSM (Fin n), PerfectCorrect P f → SupportPrivate P f →
        ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
          A * (n : ℝ) ≤ (transcriptLength P x r : ℝ) := by sorry

end SymmetricPSM1041.ORLowerBound
