-- Prove2me | Theorems.Thm_Poly1305_prime_p2
-- name    : Poly1305.prime_p2
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T07:40:42.088887+00:00
-- url     : https://prove2.me/theorems/0ca65b0c-b283-4144-a2e3-5e4b116eaaf0
-- title:
--   Proof of Theorem 3.1 — p₂ is prime
-- statement:
--   $222890620702$ divides $p_1 - 1$, and $p_2 = (p_1 - 1)/222890620702 = 4024685905107147541$ is prime, where $p_1 = (2^{130} - 6)/1517314646$.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, proof of Theorem 3.1 (p₂ is prime)

import Mathlib.Data.Nat.Prime.Defs
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem prime_p2 : 222890620702 ∣ p1 - 1 ∧ p2.Prime := by
  sorry

end Poly1305
