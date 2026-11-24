-- Prove2me | Theorems.Thm_Poly1305_theorem_3_2
-- name    : Poly1305.theorem_3_2
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T07:42:23.806053+00:00
-- url     : https://prove2.me/theorems/16f9a7b6-914a-467d-92d1-e15b7dc17a2b
-- title:
--   Theorem 3.2 — if m′ − m − u is zero modulo 2^130 − 5 then m = m′
-- statement:
--   For messages $m, m'$ and an integer $u$: if the integer polynomial $m' - m - u$ (with $m = c_1 x^q + \dots + c_q x^1$ as on p. 7, `poly`, and $u$ a constant polynomial) maps to the zero polynomial over $\mathbb{Z}/(2^{130} - 5)$, then $m = m'$.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, Theorem 3.2

import Mathlib.Data.ZMod.Defs
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem theorem_3_2 (m m' : Message) (u : ℤ)
    (h : (poly m' - poly m - Polynomial.C u).map (Int.castRingHom (ZMod p1305)) = 0) :
    m = m' := by
  sorry

end Poly1305
