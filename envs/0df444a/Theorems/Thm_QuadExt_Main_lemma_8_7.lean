-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_8_7
-- name    : QuadExt.Main.lemma_8_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:02:54.662099+00:00
-- url     : https://prove2.me/theorems/d8f2e81a-1a5a-45a3-8203-333ef5485f54
-- title:
--   Lemma 8.7 — $\operatorname{rank} P(\beta) \le r$ forces multiplicity $\ge k - r$ of $\beta$ as a root of $\det P(t)$
-- statement:
--   Let $F$ be a field and $P(t) \in F[t]^{k \times k}$ a matrix of polynomials with $\det P(t) \ne 0$. If $\beta \in F$ satisfies $\operatorname{rank}_F P(\beta) \le r$, then $\beta$ is a root of $\det P(t)$ of multiplicity at least $k - r$:
--   $$\operatorname{mult}_\beta\big(\det P(t)\big) \ge k - r .$$
--   In the proof of Theorem 8.5 this converts "many bad field elements" into "a determinant polynomial with too many roots".
--
--   Differences from the source:
--   - encoding: $k - r$ → computed in $\mathbb Z$, $r$ a natural number; reason: avoids truncated subtraction (for $r \ge k$ the claim is trivial either way).
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 28 (PDF 29), Lemma 8.7

import Mathlib

namespace QuadExt.Main

open Polynomial in
/-- **Lemma 8.7** (p. 28): if `P(t) ∈ F[t]^{k×k}` has non-zero determinant and `β ∈ F` has
`rank_F P(β) ≤ r`, then `β` is a root of `det P(t)` of multiplicity at least `k − r`. -/
theorem lemma_8_7 {F : Type} [Field F] (k r : ℕ) (P : Matrix (Fin k) (Fin k) F[X])
    (hP : P.det ≠ 0) (β : F) (hrank : (P.map fun q => q.eval β).rank ≤ r) :
    (k : ℤ) - r ≤ (P.det.rootMultiplicity β : ℤ) := by sorry

end QuadExt.Main
