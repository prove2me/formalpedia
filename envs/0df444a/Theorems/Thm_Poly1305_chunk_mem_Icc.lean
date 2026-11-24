-- Prove2me | Theorems.Thm_Poly1305_chunk_mem_Icc
-- name    : Poly1305.chunk_mem_Icc
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T07:39:15.627936+00:00
-- url     : https://prove2.me/theorems/4c3a5820-50f9-4a24-9e6f-073a017c7048
-- title:
--   §2 — each c_i lies in {1, …, 2^129}
-- statement:
--   For every message $m$ and every $i$ with $1 \le i \le q = \lceil \ell/16 \rceil$, the integer $c_i$ of p. 4 (`chunk m i`) satisfies $1 \le c_i \le 2^{129}$.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 4, §2, Conversion and padding (c_i ∈ {1, …, 2^129})

import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem chunk_mem_Icc (m : Message) (i : ℕ) (hi : 1 ≤ i) (hiq : i ≤ numChunks m) :
    1 ≤ chunk m i ∧ chunk m i ≤ 2 ^ 129 := by
  sorry

end Poly1305
