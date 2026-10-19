-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_corollary_1_trad
-- name    : PlatformToken.SmallCost.corollary_1_trad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:01.853322+00:00
-- url     : https://prove2.me/theorems/9afa386f-120d-4373-aa5f-640872665f1e
-- title:
--   Corollary 1, $i=\$$: Lemma 2's program equals (37)–(38)
-- statement:
--   Assume the standing assumptions of the model and $K>0$. Then the traditional payoff $\Pi^\$$ defined by Lemma 2's program (17)–(20) equals the value of Corollary 1's program
--   $$\max\Bigl\{0,\ \sup_{Q>0,\,e>0}\Bigl[\frac{\mathcal F(e,Q)}{1-\delta}-cQ-C(Q)-\gamma e\Bigr]\Bigr\}\quad\text{s.t.}\quad \beta^\$\frac{\mathcal F_e(e,Q)}{1-\delta}=\gamma,$$
--   with $\beta^\$$ given by the two-case formula (40).
--
--   The equity share $\alpha$ of (19) is eliminated: $1-\alpha=\beta^\$$ in both cases of (40).
--
--   **Formalization Note** The printed interiority hypothesis is part of the programs. The assumption $K>0$ is added: at $K=0$, (19) gives $\alpha=0$ on the branch $c\le d-s$, which (20) forbids, while (38) remains feasible. The statement is an equality of payoffs, not of feasible sets: the sets can differ at points with $\mathcal F(e,Q)\le 0$, where the objective is negative.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 10, Corollary 1, (37)–(38), (40), case i = $

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Programs
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Corollary 1, i = $** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 10, Corollary 1, (37)–(38), (40)).

For a positive capacity-cost scale `K`, the entrepreneur's equilibrium payoff `Π^$` of Lemma 2's
program (17)–(20) equals the value of Corollary 1's program (37)–(38) with `β^$` of (40).

**Formalization Note.**
* The printed interiority hypothesis "Suppose Q̄ > 0, ē > 0" is built into the programs and
  dropped.
* `0 < K` is added: at `K = 0`, (19) gives `α = 0` on the branch `c ≤ d - s`, which (20) excludes,
  while (37)–(38) stay feasible (the paper's proof says "α ∈ [0, 1]", p. 19, against (20)'s
  `0 < α < 1`).
* This is an equality of the payoffs, not of feasible sets: at points with `F(e,Q) ≤ 0` the two
  programs can differ, but the objective is negative there.
-/
theorem corollary_1_trad (p : Params) (hp : p.Standing) (hK : 0 < p.K) :
    PiTrad p = PiCor1Trad p := by sorry

end PlatformToken.SmallCost
