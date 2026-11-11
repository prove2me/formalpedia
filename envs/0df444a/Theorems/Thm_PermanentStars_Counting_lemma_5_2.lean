-- Prove2me | Theorems.Thm_PermanentStars_Counting_lemma_5_2
-- name    : PermanentStars.Counting.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:34.791964+00:00
-- url     : https://prove2.me/theorems/cbf81593-8bbb-4729-8a78-d1c886b0faf3
-- title:
--   Lemma 5.2 — Counting subsets with a forced prefix
-- statement:
--   Let $N\ge0$ and $r\ge1$ be integers, and let $c$ be real with $1<c<2$ and $c(c-1)^{r-1}\ge1$. For $S\subseteq[N]$, let $\operatorname{pref}(S)$ be the largest initial-segment length contained in $S$. Then
--   $$\#\{S\subseteq[N]:|S|\le r\operatorname{pref}(S)\}\le(N+1)c^N.$$
--   The empty subset and the full prefix are included. This bounds the covered-set choices of the small-star dynamic program.
--
--   Differences from the source:
--   - encoding: cardinality bars around the subset family in (19) → Finset.card of all subsets satisfying the prefix condition; reason: finite subsets of Fin N represent exactly the source family; the PDF already displays cardinality bars, which the text extraction loses
--   - encoding: initial segment [p] → indices i in Fin N with i.val<p; reason: this is the same ordered prefix after shifting indices by one
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Lemma 5.2, PDF/printed p.10

import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting

/-- Lemma 5.2, (19), p.10; braces are a cardinality, as in its counting proof. -/
theorem lemma_5_2 (N r : ℕ) (hr : 1 ≤ r) (c : ℝ)
    (hc : 1 < c) (hc2 : c < 2) (hprod : 1 ≤ c * (c - 1) ^ (r - 1)) :
    (prefixCount N r : ℝ) ≤ (N + 1 : ℝ) * c ^ N := by sorry

end PermanentStars.Counting
