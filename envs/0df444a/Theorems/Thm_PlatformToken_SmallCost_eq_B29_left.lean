-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_eq_B29_left
-- name    : PlatformToken.SmallCost.eq_B29_left
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:00.756285+00:00
-- url     : https://prove2.me/theorems/0b3b890c-c162-4ea5-9534-a1258ff42a7c
-- title:
--   Proof of Proposition 2, (B.29): $e^\$(Q)<e^B(Q)$
-- statement:
--   Assume the standing assumptions, $c>0$ or $m>0$, and $K>0$. Let $Q>0$ and let $e_1>0$ satisfy $d(e_1,Q)>s(Q)$ and $g(e_1,Q)=0$. Then there is $e_2>e_1$ with
--   $$h(e_2,Q)=0.$$
--
--   Applied to the largest roots $e^\$(Q)$ of $g(\cdot,Q)=0$ on $(e^\dagger(Q),\infty)$ and $e^B(Q)$ of $h(\cdot,Q)=0$, this is the first inequality $e^\$(Q)<e^B(Q)$ of (B.29).
--
--   **Formalization Note** The inequality is stated in root form rather than through a definition of "the largest root".
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2, (B.29), first inequality

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Proof of Proposition 2, (B.29), first inequality** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2,
(B.29): `e^$(Q) < e^B(Q)`).

`e^$(Q)` and `e^B(Q)` are the largest roots of `g(·,Q) = 0` on `(e†(Q), ∞)` and of
`h(·,Q) = 0`. Root form: every root `e₁` of `g(·,Q)` with `d(e₁,Q) > s(Q)` is exceeded by a root
`e₂` of `h(·,Q)`; applied to the largest roots this is `e^$(Q) < e^B(Q)`.

**Formalization Note.** Stated in root form to avoid defining "the largest root" by a `sSup` with a
junk value; `0 < K` and `0 < c ∨ 0 < m` are the hypotheses of `claim_i_h_gt_g`, which the printed
argument uses.
-/
theorem eq_B29_left (p : Params) (hp : p.Standing) (hcm : 0 < p.c ∨ 0 < p.m)
    (hK : 0 < p.K) (Q e₁ : ℝ) (hQ : 0 < Q) (he₁ : 0 < e₁) (hsd : s p Q < d p e₁ Q)
    (hg : g p e₁ Q = 0) :
    ∃ e₂, e₁ < e₂ ∧ h p e₂ Q = 0 := by sorry

end PlatformToken.SmallCost
