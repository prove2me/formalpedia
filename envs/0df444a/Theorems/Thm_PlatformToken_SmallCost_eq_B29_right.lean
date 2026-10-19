-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_eq_B29_right
-- name    : PlatformToken.SmallCost.eq_B29_right
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:55.347952+00:00
-- url     : https://prove2.me/theorems/7d0ac932-ffb0-4527-8854-816c93dd497f
-- title:
--   Proof of Proposition 2, (B.29): $e^B(Q)<e^*(Q)$
-- statement:
--   Assume the standing assumptions and $K>0$. For every $Q>0$ and every $e>0$ with $h(e,Q)=0$,
--   $$e<e^*(Q)=\Bigl(\frac{aQ^{1-b}}{(1-\delta)\gamma}\Bigr)^{1/(1-a)}.$$
--
--   In particular the blockchain effort $e^B(Q)$ lies strictly below the unconstrained optimal effort, the second inequality of (B.29).
--
--   **Formalization Note** $K>0$ is needed: at $K=0$, $h(e,Q)=\mathcal F_e(e,Q)/(1-\delta)-\gamma$ and its root is $e^*(Q)$ itself.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2, (B.29), second inequality

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Proof of Proposition 2, (B.29), second inequality** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2,
(B.29): `e^B(Q) < e*(Q)`).

For `K > 0` and `Q > 0`, every root `e > 0` of `h(·,Q)` lies strictly below
`e*(Q) = (a Q^{1-b}/((1 - δ) γ))^{1/(1-a)}`.

**Formalization Note.** `e*(Q)` is the closed form `estar`; that it is the printed argmax is
`claim_ii_concave`. `0 < K` is added: at `K = 0`, `h(e,Q) = F_e(e,Q)/(1 - δ) - γ` and its root is
`e*(Q)` itself.
-/
theorem eq_B29_right (p : Params) (hp : p.Standing) (hK : 0 < p.K) (Q e : ℝ) (hQ : 0 < Q)
    (he : 0 < e) (hh : h p e Q = 0) :
    e < estar p Q := by sorry

end PlatformToken.SmallCost
