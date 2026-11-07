-- Prove2me | Theorems.Thm_RevisitXor_claim_7_2
-- name    : RevisitXor.claim_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:54.2954+00:00
-- url     : https://prove2.me/theorems/754625ab-9244-45d5-b329-a5468c8e02a6
-- title:
--   Claim 7.(2): $\sum_z w(y\to z)=(-1)^{h(0,y)}\in\{-1,1\}$
-- statement:
--   For every fixed $h:[2]^{2m}\to[2]$ and every $y\in[2]^m$,
--
--   $$\sum_{z\in[2]^m}w(y\to z)=(-1)^{h(0,y)}\in\{-1,1\}.$$
--
--   Summing the row of weights of $y$ kills every $x\ne0$; this bounds $\mathbb E[W]$ in Lemma 6.
--
--   **Formalization Note** $h(0,y)$ is $h$ at $x=0$.
--
--   Differences from the source: none.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Claim 7.(2), p.7

import Mathlib
import Definitions.Def_RevisitXor_wEdge

namespace RevisitXor

/-- **Claim 7.(2).** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Claim 7, p.7: "2. For every y, Σ_{z∈[2]^m} w(y → z) = (−1)^{h(0,y)} ∈ {−1, 1}."

**Formalization Note.** `h(0, y)` is `h` at `x = 0`; `(−1)^b` is `sgn b`. Both the identity and the
membership in `{−1, 1}` are stated. -/
theorem claim_7_2 {m : ℕ} (h : Cube m × Cube m → ZMod 2) (y : Cube m) :
    ∑ z : Cube m, wDir h y z = sgn (h (0, y)) ∧
      (sgn (h (0, y)) = -1 ∨ sgn (h (0, y)) = 1) := by sorry

end RevisitXor
