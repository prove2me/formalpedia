-- Prove2me | Theorems.Thm_PathORAMCap_proposition_5_3
-- name    : PathORAMCap.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:44.8814+00:00
-- url     : https://prove2.me/theorems/a39d47eb-111c-4626-80bc-1542561b59f7
-- title:
--   Proposition 5.3 — $\mathbb E[F_v]>5$ for $H=14$, $K=32$, $d\ge30$, $d+19\le L$, $n=2^{d+19}$
-- statement:
--   Let $N=2^L$ and $\pi=P_{3,N}(N,(1,\dots,N))$. Choose $H=14$, $K=32$ and integers $d,n$ with
--
--   $$d\ge30,\qquad d+19\le L,\qquad n=2^{d+19}.$$
--
--   Then for every node $v$ at depth $d$ the capped local overflow (44) satisfies $\mathbb E[F_v]>5$.
--
--   Each region thus sends on average more than five blocks upward, more than the three slots per ancestor bucket that Lemma 5.2 subtracts.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: §5's full scan π = P_{3,N}(N, (1, …, N)) with N = 2^L and its reverse blocks i = 1, …, N → the scan α = id : Fin N → Fin N on Labels (2^L) (2^L); reverse block i is the block with Fin value N − i; reason: the same process; address N − i + 1 is Fin value N − i
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Proposition 5.3, p.38 (PDF p.41), eq. (45); restated p.39 (PDF p.42)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST
import Definitions.Def_PathORAMCap_regionF

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Proposition 5.3** (Surplus in a Real Scan Region; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.38 (PDF p.41)): "Let N = 2^L and
π = P3,N(N, (1, . . . , N)). Choose H = 14, K = 32, and integers d, n satisfying d ≥ 30, d + 19 ≤ L,
n = 2^(d+19). (45) For every node v at depth d, the quantity in (44) satisfies E[Fv] > 5."

**Formalization Note.** `F_v` is `regionF L 14 32 (2^(d+19))` at the node `v`; `E` is the uniform
average over the scan's labels. -/
theorem proposition_5_3 (L d : ℕ) (hd : 30 ≤ d) (hdL : d + 19 ≤ L) (v : Leaf d) :
    5 < mean (fun ω : Labels (2 ^ L) (2 ^ L) => regionF L 14 32 (2 ^ (d + 19)) ω v.toList) := by sorry

end PathORAMCap
