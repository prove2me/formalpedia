-- Prove2me | Theorems.Thm_RevisitXor_claim_7_1
-- name    : RevisitXor.claim_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:08.35966+00:00
-- url     : https://prove2.me/theorems/6bb9781e-8558-423c-86e1-07dd7bdeb9ff
-- title:
--   Claim 7.(1): $|w(x\to y)|\le1$
-- statement:
--   For every fixed $h:[2]^{2m}\to[2]$ and every $x,y\in[2]^m$,
--
--   $$|w(x\to y)|\le1 .$$
--
--   The weights are averages of signs; this bound feeds the boundedness clause of Lemma 6.
--
--   Differences from the source: none.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Claim 7.(1), p.7

import Mathlib
import Definitions.Def_RevisitXor_wEdge

namespace RevisitXor

/-- **Claim 7.(1).** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Claim 7, p.7: "Claim 7. We have: 1. |w(x → y)| ≤ 1 for every x, y."

**Formalization Note.** `w(x → y)` is `wDir h x y` for a fixed `h : [2]^m × [2]^m → [2]`. -/
theorem claim_7_1 {m : ℕ} (h : Cube m × Cube m → ZMod 2) (x y : Cube m) :
    |wDir h x y| ≤ 1 := by sorry

end RevisitXor
