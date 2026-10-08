-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_small_X_lt_gNum
-- name    : TuranMatching.ColorCritical.small_X_lt_gNum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:54.486052+00:00
-- url     : https://prove2.me/theorems/31735a34-d0e3-436d-8ae3-5c80cf166ec3
-- title:
--   Proof of Prop. 3.1, p. 5 — (s−1)n + 2(s+1)s < g(n,k,s) for n > 3s² + 2s
-- statement:
--   Let $k\ge 2$, $s\ge 1$ and $n>3s^2+2s$. Then
--   $$(s-1)\,n+2(s+1)\,s<g(n,k,s),$$
--   where $g(n,k,s)$ is the number of edges of the complete $k$-partite graph $G(n,k,s)$.
--
--   Together with the previous bound, this shows that a graph with fewer than $s$ vertices of degree exceeding $2s$ has fewer edges than $G(n,k,s)$, so the proof of Proposition 3.1 may assume that exactly $s$ vertices have degree exceeding $2s$.
--
--   **Formalization Note** The page says "for $n$ exceeding, say, $3s^2$". That threshold is too small: for $k=2$, $s=2$, $n=13$ the left side is $25$ while $g(13,2,2)=22$, and it fails for $k=2$ and every $s\ge 1$. The statement uses the threshold $3s^2+2s$, which follows from $g(n,k,s)\ge s(n-s)$; the paper's $n_0(s)$ is unspecified, so Proposition 3.1 is unaffected.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, third paragraph, fourth sentence (threshold corrected from 3s² to 3s² + 2s)

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem small_X_lt_gNum (n k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (hn : 3 * s ^ 2 + 2 * s < n) :
    (s - 1) * n + 2 * (s + 1) * s < TuranMatching.Clique.gNum n k s := by sorry

end TuranMatching.ColorCritical
