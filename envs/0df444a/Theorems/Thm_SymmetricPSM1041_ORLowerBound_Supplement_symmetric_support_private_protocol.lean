-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_symmetric_support_private_protocol
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.symmetric_support_private_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:51:54.711671+00:00
-- url     : https://prove2.me/theorems/ac428c03-e66a-4315-83f1-bf9f1060dcd8
-- title:
--   Theorem 32 (= Theorem 5) — support-private PSM for every symmetric function in $\tilde O(n)$
-- statement:
--   There are constants $C$, $k$ and $N\ge1$ such that for every $n\ge N$ and every symmetric Boolean function $f:\{0,1\}^n\to\{0,1\}$ there is a PSM protocol $P$ for $f$ that is perfectly correct and support private, with total cost
--
--   $$\operatorname{cost}(P)=\max_{x,r}\sum_{i=1}^n|M_i(x_i,r)|\le C\,n\log_2^k n.$$
--
--   A function is symmetric when its value depends only on the Hamming weight of its input. The constants do not depend on $f$. This is the paper's Theorem 5, stated again as Theorem 32; it limits lower-bound techniques that use only support privacy to at most a polylogarithmic factor above linear communication.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: total complexity Õ(n) → ∃ C k N, ∀ n ≥ N, ∀ symmetric f, a protocol with the stated privacy and totalCost ≤ the bound with log₂; reason: Õ(g) = O(g·polylog n), read with constants uniform over f
--   - encoding: symmetric: f(x) = g(∥x∥) → ShallowSym.IsSymmetric f: ∥x∥ = ∥y∥ → f x = f y; reason: the two definitions are equivalent
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 22, Theorem 32 (proof pp. 22–23); p. 4, Theorem 5

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_ShallowSym_IsSymmetric

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem symmetric_support_private_protocol :
    ∃ C : ℝ, ∃ k : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ f : (Fin n → Bool) → Bool, ShallowSym.IsSymmetric f →
        ∃ P : PSM (Fin n), PerfectCorrect P f ∧ SupportPrivate P f ∧
          (totalCost P : ℝ) ≤ C * (n : ℝ) * (Real.logb 2 n) ^ k := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
