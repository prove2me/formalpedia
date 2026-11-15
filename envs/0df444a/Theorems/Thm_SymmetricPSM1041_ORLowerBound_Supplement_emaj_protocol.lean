-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_emaj_protocol
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.emaj_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:49:35.983086+00:00
-- url     : https://prove2.me/theorems/4338a2a6-5771-4087-a5a5-0b02c60f76ba
-- title:
--   Theorem 27 — perfect PSM for EMAJ$_n$ of cost $O(n\log n)$
-- statement:
--   There are constants $C$ and $N\ge1$ such that for every $n\ge N$ there is a PSM protocol $P$ for $\mathrm{EMAJ}_n(x)=\mathbf 1[\|x\|=\lfloor n/2\rfloor]$ that is perfectly correct and perfectly private, with total cost
--
--   $$\operatorname{cost}(P)=\max_{x,r}\sum_{i=1}^n|M_i(x_i,r)|\le C\,n\log_2 n.$$
--
--   It matches the lower bound of Corollary 25 for exact majority.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: cost O(n log n) → ∃ C, ∃ N ≥ 1, ∀ n ≥ N, a protocol with totalCost ≤ C·n·log₂ n; reason: standard reading of an O-upper bound; the threshold excludes n = 1, where n log₂ n = 0
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 18, Theorem 27 (proof p. 18)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem emaj_protocol :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ P : PSM (Fin n), PerfectCorrect P (emajFunction n) ∧
        PerfectPrivate P (emajFunction n) ∧
        (totalCost P : ℝ) ≤ C * (n : ℝ) * Real.logb 2 n := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
