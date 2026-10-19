-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_claim_i_h_gt_g
-- name    : PlatformToken.SmallCost.claim_i_h_gt_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:05.209508+00:00
-- url     : https://prove2.me/theorems/d919d36f-aaf7-4902-9948-b3a95e7e0629
-- title:
--   Proof of Proposition 2, Claim (i): $h(e,Q)>g(e,Q)$
-- statement:
--   Assume the standing assumptions, $c>0$ or $m>0$, and $K>0$. For every $Q>0$ and $e>0$ with $d(e,Q)>s(Q)$,
--   $$g(e,Q)<h(e,Q),$$
--   where $h$ is (B.21) and $g$ is (B.26). Equivalently, at such points the blockchain effort factor $\beta^B$ exceeds the traditional factor $\beta^\$$.
--
--   This is the step of the proof of Proposition 2 that makes the traditional problem's feasible set a subset of the blockchain one.
--
--   **Formalization Note** The paper works on $(e^\dagger(Q),\infty)$, where $d(e,Q)>s(Q)$; this is the hypothesis $s(Q)<d(e,Q)$. Both $K>0$ and "$c>0$ or $m>0$" are needed: on the branch $c\le d-s$ the two functions coincide when $K=0$, or when $c=0$ and $s(Q)=0$.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2, Claim (i); h is (B.21), g is (B.26), p. 19

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Proof of Proposition 2, Claim (i)** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2, "Claim (i) is
true because h(e,Q) > g(e,Q)"; `h` is (B.21), `g` is (B.26), p. 19).

For `K > 0`, `Q > 0`, `e > 0` with `d(e,Q) > s(Q)` (the proof works on `(e†(Q), ∞)`),
`h(e,Q) > g(e,Q)`.

**Formalization Note.** Both `0 < K` and `0 < c ∨ 0 < m` are needed: on the branch `c ≤ d - s`,
`h = g` when `K = 0`, or when `c = 0` and `s(Q) = 0`.
-/
theorem claim_i_h_gt_g (p : Params) (hp : p.Standing) (hcm : 0 < p.c ∨ 0 < p.m)
    (hK : 0 < p.K) (Q e : ℝ) (hQ : 0 < Q) (he : 0 < e) (hsd : s p Q < d p e Q) :
    g p e Q < h p e Q := by sorry

end PlatformToken.SmallCost
