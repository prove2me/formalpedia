-- Prove2me | Theorems.Thm_Poly1305_poly1305_eq_add16_H
-- name    : Poly1305.poly1305_eq_add16_H
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:39:52.546311+00:00
-- url     : https://prove2.me/theorems/470a7213-b185-444e-977c-f616c299c44e
-- title:
--   §3 — Poly1305_r(m, s) = H_r(m) + s
-- statement:
--   For every natural number $r$, message $m$ and 16-byte string $s$: $\mathrm{Poly1305}_r(m, s)$ (p. 5, `poly1305`) equals $H_r(m) + s$, the sum modulo $2^{128}$ of 16-byte strings (p. 8, `add16`) with $H_r(m)$ the 16-byte representation of $(\underline{m}(r) \bmod 2^{130} - 5) \bmod 2^{128}$ (p. 7, `H`). The string $s$ is arbitrary, in the place of $\mathrm{AES}_k(n)$.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, §3, Proof of the security guarantee

import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem poly1305_eq_add16_H (r : ℕ) (m : Message) (s : Str16) :
    poly1305 r m s = add16 (H r m) s := by
  sorry

end Poly1305
