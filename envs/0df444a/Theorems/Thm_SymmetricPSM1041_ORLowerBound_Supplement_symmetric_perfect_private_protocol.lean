-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_symmetric_perfect_private_protocol
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.symmetric_perfect_private_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:51:16.65689+00:00
-- url     : https://prove2.me/theorems/f11d5b2e-1cda-4dd6-9d9f-cb89849b0908
-- title:
--   Theorem 31 (= Theorem 3) — perfect PSM for every symmetric function in $\tilde O(n^{3/2})$
-- statement:
--   There are constants $C$, $k$ and $N\ge1$ such that for every $n\ge N$ and every symmetric Boolean function $f:\{0,1\}^n\to\{0,1\}$ there is a PSM protocol $P$ for $f$ that is perfectly correct and perfectly private, with total cost
--
--   $$\operatorname{cost}(P)=\max_{x,r}\sum_{i=1}^n|M_i(x_i,r)|\le C\,n^{3/2}\log_2^k n.$$
--
--   A function is symmetric when its value depends only on the Hamming weight of its input. The constants do not depend on $f$. This is the paper's Theorem 3, stated again as Theorem 31; it improves the previously known quadratic bound.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: total complexity Õ(n^{3/2}) → ∃ C k N, ∀ n ≥ N, ∀ symmetric f, a protocol with the stated privacy and totalCost ≤ the bound with log₂; reason: Õ(g) = O(g·polylog n), read with constants uniform over f
--   - encoding: symmetric: f(x) = g(∥x∥) → ShallowSym.IsSymmetric f: ∥x∥ = ∥y∥ → f x = f y; reason: the two definitions are equivalent
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 20, Theorem 31 (proof pp. 20–22); p. 3, Theorem 3

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_ShallowSym_IsSymmetric

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem symmetric_perfect_private_protocol :
    ∃ C : ℝ, ∃ k : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ f : (Fin n → Bool) → Bool, ShallowSym.IsSymmetric f →
        ∃ P : PSM (Fin n), PerfectCorrect P f ∧ PerfectPrivate P f ∧
          (totalCost P : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) * (Real.logb 2 n) ^ k := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
