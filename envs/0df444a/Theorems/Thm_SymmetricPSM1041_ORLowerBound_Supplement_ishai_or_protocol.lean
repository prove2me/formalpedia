-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_ishai_or_protocol
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.ishai_or_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:45:37.974279+00:00
-- url     : https://prove2.me/theorems/9c7f6ff8-b100-4672-81d9-d33ac7d7a84b
-- title:
--   Theorem 11 — Ishai's perfect PSM for OR with $O(n\log n)$ communication
-- statement:
--   There are constants $C$ and $N\ge1$ such that for every $n\ge N$ there is a PSM protocol $P$ for $\mathrm{OR}_n$ that is perfectly correct and perfectly private, and whose total communication satisfies
--
--   $$\operatorname{cost}(P)=\max_{x,r}\sum_{i=1}^n|M_i(x_i,r)|\le C\,n\log_2 n.$$
--
--   A "PSM protocol" in the paper's definition (p. 6) is a perfect PSM, with perfect correctness and perfect privacy. The theorem gives the best known upper bound for OR, against which the superlinear lower bound of Theorem 1 is compared.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: C(OR) = O(n log n) → ∃ C N, ∀ n ≥ N, a perfectly correct, perfectly private protocol with totalCost ≤ C·n·log₂ n; reason: standard reading of an O-upper bound on C = min over protocols of the worst-case transcript length
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 10, Theorem 11 (proof p. 10); definition of perfect PSM p. 6

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem ishai_or_protocol :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ P : PSM (Fin n), PerfectCorrect P orFunction ∧ PerfectPrivate P orFunction ∧
        (totalCost P : ℝ) ≤ C * (n : ℝ) * Real.logb 2 n := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
