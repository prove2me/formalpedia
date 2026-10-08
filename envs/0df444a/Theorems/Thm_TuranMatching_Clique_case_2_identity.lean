-- Prove2me | Theorems.Thm_TuranMatching_Clique_case_2_identity
-- name    : TuranMatching.Clique.case_2_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:22.243863+00:00
-- url     : https://prove2.me/theorems/d33d0bda-cde8-4e1b-84b8-35d1a063a90d
-- title:
--   §2, p. 4, Case 2 — $t(s+\lfloor s/(k-1)\rfloor,k)+(n-s-\lfloor s/(k-1)\rfloor)\,s=g(n,k,s)$
-- statement:
--   Let $k\ge2$, write $m=\lfloor s/(k-1)\rfloor$, and let $n\ge s+m$. Then
--   $$t(s+m,k)+(n-s-m)\,s\;=\;g(n,k,s).$$
--
--   This is the "exactly" of Case 2: the Turán graph on the $s$ vertices of the $k-1$ small classes together with $m$ vertices of the large class, plus the remaining $n-s-m$ vertices each joined to the $s$ small-class vertices, is $G(n,k,s)$.
--
--   **Formalization Note** $\lfloor s/(k-1)\rfloor$ is natural-number division; $n-s-m$ is natural subtraction, exact under $n\ge s+m$. $g(n,k,s)$ is the edge count of the graph $G(n,k,s)$, so the identity is a genuine statement about that graph. The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 4, Case 2

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem case_2_identity (n k s : ℕ) (hk : 2 ≤ k) (hn : s + s / (k - 1) ≤ n) :
    turanNum (s + s / (k - 1)) k + (n - s - s / (k - 1)) * s = gNum n k s := by sorry

end TuranMatching.Clique
