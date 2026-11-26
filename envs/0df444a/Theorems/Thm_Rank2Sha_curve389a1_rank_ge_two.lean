-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_rank_ge_two
-- name    : Rank2Sha.curve389a1_rank_ge_two
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-25T11:40:15.486429+00:00
-- url     : https://prove2.me/theorems/b006dace-315c-4a8b-a4da-103cc2d2e0db
-- title:
--   The curve 389a1 has rank at least $2$
-- statement:
--   Let $E$ be the elliptic curve over $\mathbb{Q}$ given by
--
--   $$
--   E : \; y^2 + y = x^3 + x^2 - 2x ,
--   $$
--
--   which has LMFDB label 389.a1. The Mordell–Weil group $E(\mathbb{Q})$ has rank at least $2$:
--
--   $$
--   \operatorname{rank} E(\mathbb{Q}) \ge 2 .
--   $$
--
--   The LMFDB lists the rank as exactly $2$, with the points $(0,0)$ and $(1,0)$ generating the free part. The statement here is the lower bound only, which is what the goal of the mission uses.
--
--   **Formalization Note** The rank is `Module.finrank ℤ E.Point`, which is $0$ when the rank is infinite, so the statement also asserts that the rank is finite. A proof therefore needs Mordell's theorem, which is the theorem `BSD.mordell` on this platform, or at least finiteness of the rank, in addition to two independent points.
-- source:
--   https://www.lmfdb.org/EllipticCurve/Q/389/a/1 (rank 2; generators (0,0) and (1,0))

import Mathlib
import Definitions.Def_Rank2Sha_Curves

namespace Rank2Sha
theorem curve389a1_rank_ge_two : 2 ≤ Module.finrank ℤ curve389a1.Point := by sorry
end Rank2Sha
