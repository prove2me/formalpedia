-- Prove2me | Theorems.Thm_Poly1305_security_constant_bound
-- name    : Poly1305.security_constant_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:40:12.000605+00:00
-- url     : https://prove2.me/theorems/cfc1c8ce-75ca-48a7-b0df-6cf7faacbba4
-- title:
--   §3 — (1 − C/2^128)^(−(C+1)/2) ≤ 1.649 for C ≤ 2^64, and 1.649 · 8 < 14
-- statement:
--   For every natural number $C \le 2^{64}$, the real number $(1 - C/2^{128})^{-(C+1)/2}$ (a real power of a positive base) is at most $1.649$; and $1.649 \cdot 8 < 14$.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 7, §3, Security guarantee (C ≤ 2^64)

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Poly1305

theorem security_constant_bound :
    (∀ C : ℕ, C ≤ 2 ^ 64 →
      (1 - (C : ℝ) / 2 ^ 128) ^ (-((C : ℝ) + 1) / 2) ≤ 1.649) ∧
    (1.649 : ℝ) * 8 < 14 := by
  sorry

end Poly1305
