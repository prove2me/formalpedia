-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_theorem_1_1
-- name    : SublinearChoresMMS.Disposal.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:30:46.632719+00:00
-- url     : https://prove2.me/theorems/e5ebe349-c0fc-4955-acf9-8d87eeb8bfaf
-- title:
--   Theorem 1.1 — ex-ante PROP, ex-post MMS1 and sublinear MMS exceptions
-- statement:
--   There is one universal real constant $C>0$ with the following property. For every $n\ge1$, every finite chore set $M$ of size $m\ge0$, and every profile of nonnegative real additive costs, there is a finite probability law $P$ on complete allocations such that every agent is proportional in expectation:
--
--   $$\mathbb E_P[c_i(X_i)]\le\frac{c_i(M)}n\quad\text{for every }i.$$
--
--   In every allocation of positive probability, every agent receives an MMS1 bundle relative to her MMS on the original full chore set, and
--
--   $$\#\{i:c_i(X_i)>\mu_i\}\le Cn^{3/4}(\log(2n))^{1/4}.$$
--
--   All clauses concern the same lottery. Costs may be zero, ties are permitted, some or all MMS values may vanish, empty bundles are allowed, and there may be no chores. No normalization, IDO restriction, structured packing, or favorable coefficient law is assumed. Deleting at most one chore from each exceptional bundle then yields exact MMS with sublinearly many disposals, evaluated against the original benchmarks; proportionality is asserted before any deletion.
--
--   Differences from the source:
--   - reading: all but O-tilde(n^(3/4)) agents are MMS → at most C*n^(3/4)*(log(2*n))^(1/4) non-MMS agents in each supported allocation, with C before all instance data; reason: Section 3.4 gives this logarithmic power via q, k and K+3k+2; enlarging a universal C and using log(2n) covers all positive bounded n
--   - encoding: finite agents, chores, complete partitions and finite lotteries → agents Fin n, chores Fin m, allocation maps and normalized finite lists with real weights; reason: bijections identify the same finite instances and partitions; repeated lottery atoms may be merged and positive weights define support
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Theorem 1.1, printed p. 1 / PDF p. 2; §3.4 proof, printed p. 13 / PDF p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Lin–Wu–Zhou, STOC 2027 submission #845 (October 2026), Theorem 1.1,
printed p. 1 / PDF p. 2; explicit logarithmic rate from §3.4, printed p. 13 / PDF p. 14.
No normalization, ordering, strict positivity, or packing certificate is assumed. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 0 < n → ∀ c : Cost n m,
      Nonnegative c → ∃ P : FiniteLaw (Allocation n m),
        (∀ i, P.mean (fun X => cost c i (bundle X i)) ≤ propShare c i) ∧
        ∀ a : Fin P.size, 0 < P.weight a →
          (∀ i, MMS1 c i (bundle (P.atom a) i)) ∧
          ((nonMMS c (P.atom a)).card : ℝ) ≤
            C * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (2 * (n : ℝ))) ^ (1 / 4 : ℝ) := by sorry

end SublinearChoresMMS.Disposal
