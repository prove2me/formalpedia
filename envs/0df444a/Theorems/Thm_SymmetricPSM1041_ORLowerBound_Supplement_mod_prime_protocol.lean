-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_mod_prime_protocol
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.mod_prime_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:48:58.098949+00:00
-- url     : https://prove2.me/theorems/1431e3bc-fa6c-45cb-ad97-1e7b8352605e
-- title:
--   Theorem 26 — perfect PSM for MOD$_{q,n}$, $q$ prime, of cost $O(n\log q)$
-- statement:
--   There is a constant $C$ such that for every prime $q$ and every $n\ge0$ there is a PSM protocol $P$ for $\mathrm{MOD}_{q,n}(x)=\mathbf 1[\|x\|\equiv0\pmod q]$ that is perfectly correct and perfectly private, with total cost
--
--   $$\operatorname{cost}(P)=\max_{x,r}\sum_{i=1}^n|M_i(x_i,r)|\le C\,n\log_2 q.$$
--
--   The bound is uniform in both $n$ and $q$. It matches the lower bound of Corollary 25 for prime $q$.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: cost O(n log q) for prime q → ∃ C, ∀ prime q, ∀ n, a protocol with totalCost ≤ C·n·log₂ q; reason: the O-bound read in both parameters, uniformly; the paper's protocol has cost n⌈log q⌉ ≤ 2 n log₂ q, and n = 0 is the trivial protocol
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 18, Theorem 26 (proof p. 18)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem mod_prime_protocol :
    ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ n : ℕ,
      ∃ P : PSM (Fin n), PerfectCorrect P (modFunction q n) ∧
        PerfectPrivate P (modFunction q n) ∧
        (totalCost P : ℝ) ≤ C * (n : ℝ) * Real.logb 2 q := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
