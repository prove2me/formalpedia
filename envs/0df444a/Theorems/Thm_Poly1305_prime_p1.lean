-- Prove2me | Theorems.Thm_Poly1305_prime_p1
-- name    : Poly1305.prime_p1
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T07:41:22.114715+00:00
-- url     : https://prove2.me/theorems/7595192f-8036-408c-9522-88cbb9cfeea6
-- title:
--   Proof of Theorem 3.1 — p₁ is prime
-- statement:
--   $1517314646$ divides $2^{130} - 6$, and $p_1 = (2^{130} - 6)/1517314646 = 897064739519922787230182993783$ is prime.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, proof of Theorem 3.1 (p₁ is prime)

import Mathlib.Data.Nat.Prime.Defs
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem prime_p1 : 1517314646 ∣ 2 ^ 130 - 6 ∧ p1.Prime := by
  sorry

end Poly1305
