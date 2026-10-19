-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_eq_B19_relax
-- name    : PlatformToken.SmallCost.eq_B19_relax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:00.901708+00:00
-- url     : https://prove2.me/theorems/6710365d-5a5b-4843-9c3f-1bb46563bb54
-- title:
--   Proof of Proposition 2, (B.19)–(B.20): for small $K$ the token-financing cap (39) can be relaxed
-- statement:
--   Assume the standing assumptions and $c>0$ or $m>0$. Then there is $\varepsilon>0$ such that for every capacity-cost scale $K\in(0,\varepsilon]$ (all other parameters fixed) the value of Corollary 1's blockchain program (37)–(39) equals the value of the relaxed program
--   $$\max\Bigl\{0,\ \sup_{Q>0,\,e>0}\Bigl[\frac{\mathcal F(e,Q)}{1-\delta}-cQ-C(Q)-\gamma e\Bigr]\Bigr\}\quad\text{s.t.}\quad h(e,Q)=0,\qquad (B.19)\text{–}(B.20)$$
--   where $h(e,Q)=\bigl(1-(1-\delta)C(Q)/(d(e,Q)Q)\bigr)\mathcal F_e(e,Q)/(1-\delta)-\gamma$ (B.21).
--
--   That is, the constraint $d(e,Q)Q\ge vC(Q)$ does not bind when capacity is cheap.
--
--   **Formalization Note** The paper argues "If $K=0$ then $d(e,Q)Q>vC(Q)$. By continuity, this is also true when $K\in(0,\varepsilon)$." The equality of the two values is the precise content of "we can relax (39)". The hypothesis $c>0$ or $m>0$ is the one added to Proposition 2.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 19, proof of Proposition 2, (B.19)–(B.21)

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Proof of Proposition 2, (B.19)–(B.20)** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 19, proof of Proposition 2,
(B.19)–(B.21)).

For sufficiently small capacity cost `K > 0`, the cap (39), `d(e,Q) Q ≥ v C(Q)`, can be relaxed:
the value of Corollary 1's blockchain program equals the value of (B.19)–(B.20), the same
program with constraint (39) dropped.

**Formalization Note.**
* The printed "If K = 0 then d(e,Q)Q > vC(Q). By continuity, this is also true when K ∈ (0, ε)"
  is pointwise trivial; its content is that (39) does not bind near the optimum uniformly for
  small `K`. The payoff equality is the precise form of "we can relax (39)".
* `0 < c ∨ 0 < m` is the goal's added hypothesis; with `c = m = 0` the relaxed objective is not
  controlled as `K → 0`.
-/
theorem eq_B19_relax (p : Params) (hp : p.Standing) (hcm : 0 < p.c ∨ 0 < p.m) :
    ∃ ε > 0, ∀ K ∈ Set.Ioc 0 ε, PiCor1B (withK p K) = PiCor1BRelaxed (withK p K) := by sorry

end PlatformToken.SmallCost
