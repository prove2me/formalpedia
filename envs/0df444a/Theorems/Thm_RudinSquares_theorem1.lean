-- Prove2me | Theorems.Thm_RudinSquares_theorem1
-- name    : RudinSquares.theorem1
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:26:53.062204+00:00
-- url     : https://prove2.me/theorems/5db36991-ca8d-4932-94e8-df88546d24b4
-- title:
--   Theorem 1 — Strong and Super-Strong Rudin conjectures up to $N=52$
-- statement:
--   The main result of the paper (Theorem 1), in two parts. Let $Q(N)$ be the maximum number of squares among the first $N$ terms of a non-trivial integer arithmetic progression, and $Q(N;q,a)$ the number of squares among $qn+a$, $n=0,\dots,N-1$. Write $GP_k=k(3k-1)/2$ for the generalized pentagonal numbers.
--
--   **(S) Strong Rudin conjecture, verified range.** For every integer $N$ with $6\le N\le 52$,
--   $$Q(N)=Q(N;24,1).$$
--
--   **(SS) Super-Strong Rudin conjecture, verified range.** If $8\le N=GP_k+1\le 52$ for some integer $k$, then for all integers $q,a$ with $\gcd(q,a)$ squarefree and $q\ge 0$,
--   $$Q(N)=Q(N;q,a)\quad\Longleftrightarrow\quad (q,a)=(24,1).$$
--
--   Thus in the verified range the progression $24n+1$ is extremal, and at the jump lengths $N=GP_k+1$ it is the unique extremal progression (with squarefree gcd and $q\ge0$). This is the mission's goal theorem.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, Theorem 1, p. 59.

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem theorem1 :
    (∀ N : ℕ, 6 ≤ N → N ≤ 52 → Q N = Qap N 24 1) ∧
    (∀ N : ℕ, (∃ k : ℤ, (N : ℤ) = GP k + 1 ∧ 8 ≤ N ∧ N ≤ 52) →
      ∀ q a : ℤ, Squarefree (Int.gcd q a) → 0 ≤ q →
        (Q N = Qap N q a ↔ q = 24 ∧ a = 1)) := by sorry
end RudinSquares
