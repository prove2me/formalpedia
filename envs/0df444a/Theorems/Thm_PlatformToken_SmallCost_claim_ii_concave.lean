-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_claim_ii_concave
-- name    : PlatformToken.SmallCost.claim_ii_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:04.572025+00:00
-- url     : https://prove2.me/theorems/37e45928-3753-43d2-baa9-228d4f3f5945
-- title:
--   Proof of Proposition 2, Claim (ii): the objective is strictly concave in $e$ with maximizer $e^*(Q)$
-- statement:
--   Assume the standing assumptions and let $Q>0$. Then
--   1. $e\mapsto \mathcal F(e,Q)/(1-\delta)-cQ-C(Q)-\gamma e$ is strictly concave on $[0,\infty)$;
--   2. $e^*(Q)=\bigl(aQ^{1-b}/((1-\delta)\gamma)\bigr)^{1/(1-a)}>0$;
--   3. for every $e\ge 0$ with $e\ne e^*(Q)$,
--   $$\frac{\mathcal F(e,Q)}{1-\delta}-cQ-C(Q)-\gamma e<\frac{\mathcal F(e^*(Q),Q)}{1-\delta}-cQ-C(Q)-\gamma e^*(Q).$$
--
--   So $e^*(Q)$ is the unique argmax of the objective in (B.29), and the objective increases in $e$ below it.
--
--   **Formalization Note** The domain is $e\ge 0$ (effort levels); real powers of negative numbers are not the paper's functions.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2, Claim (ii) and (B.29)

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Proof of Proposition 2, Claim (ii)** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 20, proof of Proposition 2, (B.29)).

For `Q > 0` the objective `F(e,Q)/(1 - δ) - cQ - C(Q) - γe` is strictly concave in `e ≥ 0`, and
`e*(Q) = (a Q^{1-b}/((1 - δ) γ))^{1/(1-a)}` is positive and its unique maximizer over `e ≥ 0`.

**Formalization Note.** The printed "argmax_e" is over effort levels `e ≥ 0`; Lean's `rpow` of a
negative base is not the paper's function, so the domain is `Set.Ici 0`. The last two conjuncts
make the closed form `estar` the printed argmax.
-/
theorem claim_ii_concave (p : Params) (hp : p.Standing) (Q : ℝ) (hQ : 0 < Q) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun e => obj p e Q) ∧ 0 < estar p Q ∧
      ∀ e, 0 ≤ e → e ≠ estar p Q → obj p e Q < obj p (estar p Q) Q := by sorry

end PlatformToken.SmallCost
