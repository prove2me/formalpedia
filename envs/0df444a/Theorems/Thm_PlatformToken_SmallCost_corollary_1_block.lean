-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_corollary_1_block
-- name    : PlatformToken.SmallCost.corollary_1_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:07.245985+00:00
-- url     : https://prove2.me/theorems/6d4a3767-9a99-4280-bd44-c27f0ca369f9
-- title:
--   Corollary 1, $i=B$: Lemma 3's program equals (37)–(39)
-- statement:
--   Assume the standing assumptions of the model. The set of objective values
--   $$\frac{\mathcal F(e,Q)}{1-\delta}-cQ-C(Q)-\gamma e$$
--   attained over the feasible set of Lemma 3, (34)–(36), equals the set attained over the pairs $(Q,e)$ with $Q>0$, $e>0$,
--   $$\beta^B\frac{\mathcal F_e(e,Q)}{1-\delta}=\gamma\qquad\text{and}\qquad d(e,Q)Q\ge vC(Q),$$
--   where $\beta^B=1-(1-\delta)C(Q)/(d(e,Q)Q)$. Consequently the blockchain payoff $\Pi^B$ of Lemma 3 equals the value of Corollary 1's program (37)–(39) for $i=B$.
--
--   This is the bridge from the game-theoretic characterization of Lemma 3 to the single-program form used in the proof of Proposition 2.
--
--   **Formalization Note** The printed interiority hypothesis "Suppose $\tilde Q>0$ and $\tilde e>0$" is part of the programs and is not a separate hypothesis. Lemma 3's (36) allows $Q=0$ or $e=0$; such points violate (34) because $\gamma>0$.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 10, Corollary 1, (37)–(40), case i = B

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Programs
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Corollary 1, i = B** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 10, Corollary 1, (37)–(39)).

Lemma 3's program (33)–(36) and Corollary 1's program (37)–(39) with `β^B` of (40) have the same
set of attainable objective values; in particular `Π^B` can be written as (37)–(39).

**Formalization Note.**
* The printed hypothesis "Suppose Q̃ > 0 and ẽ > 0" (interiority of the equilibrium) is built into
  the programs and dropped; (36)'s `Q ≥ 0, e ≥ 0` points with `Q = 0` or `e = 0` violate (34)
  because `γ > 0` (with Lean's `0 ^ y = 0`).
* The first conjunct (equality of the images of the objective) is stronger than the payoff
  equality, which is the second conjunct.
-/
theorem corollary_1_block (p : Params) (hp : p.Standing) :
    (fun x : ℝ × ℝ × ℝ => obj p x.2.2 x.1) '' BlockFeasible p =
        (fun y : ℝ × ℝ => obj p y.2 y.1) '' Cor1FeasibleB p ∧
      PiBlock p = PiCor1B p := by sorry

end PlatformToken.SmallCost
