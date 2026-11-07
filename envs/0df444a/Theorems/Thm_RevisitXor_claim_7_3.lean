-- Prove2me | Theorems.Thm_RevisitXor_claim_7_3
-- name    : RevisitXor.claim_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:06.971198+00:00
-- url     : https://prove2.me/theorems/ff51a73c-e69b-46c5-9fb4-1692dd7ad8c1
-- title:
--   Claim 7.(3): $\sum_{y,z\in R}w^2(\{y,z\})\le4|R|$
-- statement:
--   For every fixed $h:[2]^{2m}\to[2]$ and every $R\subseteq[2]^m$,
--
--   $$\sum_{y\in R,\,z\in R}w^2(\{y,z\})\le4|R| .$$
--
--   This $L^2$ bound on the weights inside a vertex set is what makes the variance of $W_i$ of order $1/r$ in Lemma 6.
--
--   **Formalization Note** The sum is over ordered pairs $(y,z)\in R\times R$, including $y=z$, where $w(\{y\})=0$.
--
--   Differences from the source: none.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Claim 7.(3), p.7

import Mathlib
import Definitions.Def_RevisitXor_wEdge

namespace RevisitXor

/-- **Claim 7.(3).** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Claim 7, p.7: "3. For every R ⊆ [2]^m, Σ_{y∈R,z∈R} w²({y, z}) ≤ 4|R|."

**Formalization Note.** The sum is over ordered pairs `(y, z) ∈ R × R`, including `y = z`, where
`w({y}) = 0`. -/
theorem claim_7_3 {m : ℕ} (h : Cube m × Cube m → ZMod 2) (R : Finset (Cube m)) :
    ∑ y ∈ R, ∑ z ∈ R, wEdge h s(y, z) ^ 2 ≤ 4 * (R.card : ℝ) := by sorry

end RevisitXor
