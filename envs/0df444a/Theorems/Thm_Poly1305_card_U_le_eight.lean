-- Prove2me | Theorems.Thm_Poly1305_card_U_le_eight
-- name    : Poly1305.card_U_le_eight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:42:47.10868+00:00
-- url     : https://prove2.me/theorems/4b261500-a529-42ba-ae8c-4cbe3ca23af5
-- title:
--   Proof of Theorem 3.3 — #U ≤ 8
-- statement:
--   For every 16-byte string $g$, the integers $x$ with $-(2^{130} - 6) \le x \le 2^{130} - 6$ and $x \equiv g \pmod{2^{128}}$ (with $g$ read as $g[0] + 2^8 g[1] + \dots + 2^{120} g[15]$) number at most 8.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 9, proof of Theorem 3.3 (#U ≤ 8)

import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem card_U_le_eight (g : Str16) :
    ((Finset.Icc (-(2 ^ 130 - 6 : ℤ)) (2 ^ 130 - 6)).filter
      (fun x => x ≡ (leVal g : ℤ) [ZMOD 2 ^ 128])).card ≤ 8 := by
  sorry

end Poly1305
