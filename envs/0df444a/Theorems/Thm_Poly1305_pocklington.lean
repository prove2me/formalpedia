-- Prove2me | Theorems.Thm_Poly1305_pocklington
-- name    : Poly1305.pocklington
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T07:40:21.439835+00:00
-- url     : https://prove2.me/theorems/26d9cb23-5925-46bd-be68-33ec7c4ecfc0
-- title:
--   External — Pocklington's theorem (as applied in the proof of Theorem 3.1)
-- statement:
--   Let $N > 1$, $F$ and $a$ be natural numbers with $F \mid N - 1$ and $N < F^2$. If $N$ divides $a^{N-1} - 1$, and for every prime $q$ dividing $F$ the number $a^{(N-1)/q} - 1$ is coprime to $N$, then $N$ is prime. (Subtraction is natural-number subtraction; for $a \ge 1$ it is the usual one.)
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, Pocklington's theorem as applied in the proof of Theorem 3.1, external: H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914–1916), 29–30

import Mathlib.Data.Nat.Prime.Defs

namespace Poly1305

theorem pocklington (N F a : ℕ) (hN : 1 < N) (hF : F ∣ N - 1) (hFN : N < F ^ 2)
    (ha : N ∣ a ^ (N - 1) - 1)
    (hq : ∀ q : ℕ, q.Prime → q ∣ F → Nat.Coprime (a ^ ((N - 1) / q) - 1) N) :
    N.Prime := by
  sorry

end Poly1305
