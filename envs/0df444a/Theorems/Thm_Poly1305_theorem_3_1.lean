-- Prove2me | Theorems.Thm_Poly1305_theorem_3_1
-- name    : Poly1305.theorem_3_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:41:53.606087+00:00
-- url     : https://prove2.me/theorems/c35f140d-9bb9-431a-9102-56cb98c16569
-- title:
--   Theorem 3.1 — 2^130 − 5 is prime
-- statement:
--   The number $2^{130} - 5$ is prime.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, Theorem 3.1

import Mathlib.Data.Nat.Prime.Defs
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem theorem_3_1 : p1305.Prime := by
  sorry

end Poly1305
