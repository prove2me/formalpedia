-- Prove2me | Theorems.Thm_TuranMatching_Clique_f_discrete_convex
-- name    : TuranMatching.Clique.f_discrete_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:33.368004+00:00
-- url     : https://prove2.me/theorems/22be9f60-bb1c-43a8-9159-2d5a3ace0868
-- title:
--   §2, p. 4, Case 4 — $f(b)=t(2s-b+1,k)+b(n-2s+b-1)$ has strictly increasing differences
-- statement:
--   Let $k\ge2$, $n\ge2s+1$, and
--   $$f(b)=t(2s-b+1,k)+b\,(n-2s+b-1).$$
--   For every $b$ with $b+2\le s-\lfloor s/(k-1)\rfloor$ (so that $b$, $b+1$ and $b+2$ all lie in the range of Case 4),
--   $$f(b+1)-f(b)\ <\ f(b+2)-f(b+1).$$
--
--   So $f$ is discretely convex on the range of Case 4, and its maximum over that range is attained at an endpoint.
--
--   **Formalization Note** $f$ is integer-valued (`fCase4`), with $2s-b+1$ a natural subtraction that is exact on the range. "Increasing" is taken strictly, as the linear part grows by $2$ and the Turán bracket shrinks by at most $1$. The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 4, Case 4 (definition of f and "f(b + 1) − f(b) is an increasing function of b")

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem f_discrete_convex (n k s b : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (hb : b + 2 ≤ s - s / (k - 1)) :
    fCase4 n k s (b + 1) - fCase4 n k s b < fCase4 n k s (b + 2) - fCase4 n k s (b + 1) := by sorry

end TuranMatching.Clique
