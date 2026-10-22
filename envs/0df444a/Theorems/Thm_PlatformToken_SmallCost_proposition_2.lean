-- Prove2me | Theorems.Thm_PlatformToken_SmallCost_proposition_2
-- name    : PlatformToken.SmallCost.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:22.322295+00:00
-- url     : https://prove2.me/theorems/93001d42-e806-4033-8396-dc33204f3287
-- title:
--   Proposition 2: for small capacity cost the blockchain-based model strictly dominates, $\Pi^B>\Pi^\$$
-- statement:
--   Fix parameters satisfying the standing assumptions of the iso-elastic model, with $c>0$ or $m>0$, and let only the capacity-cost scale $K$ in $C(Q)=KQ^k$ vary. There is $\varepsilon>0$ such that for every $K\in(0,\varepsilon]$:
--   1. the entrepreneur's objective is bounded above on the feasible sets of Lemma 2 and of Lemma 3;
--   2. the blockchain-based business model strictly dominates the traditional one,
--   $$\Pi^B>\Pi^\$,\qquad(42)$$
--   unless the venture is unfeasible, that is, $\Pi^B=\Pi^\$=0$.
--
--   Here $\Pi^\$$ and $\Pi^B$ are the equilibrium payoffs of Lemmas 2 and 3. The paper traces the dominance to two channels: token financing exposes outside investors to revenue rather than profit, so the entrepreneur keeps more of the marginal value of effort, and decentralized governance removes the first-period subsidy that the holdup problem forces on the traditional platform.
--
--   **Formalization Note** The paper states $K\in[0,\varepsilon]$; at $K=0$ the Corollary 1 payoff programs coincide on the branch $c\le d-s$ (for instance $c=0$, $m=1$), contradicting the printed strict claim. Lemma 2's literal $0<\alpha$ constraint omits that zero-investment boundary. The proof itself treats $K\in(0,\varepsilon)$, so the range is $(0,\varepsilon]$. The hypothesis $c>0$ or $m>0$ is added: with $c=m=0$ the traditional model wins for every $K>0$ (e.g. $K=0.05$ gives $\Pi^\$\approx 9.69>\Pi^B\approx5.09$). The boundedness conjuncts make the suprema in $\Pi^\$$, $\Pi^B$ genuine.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 11, Proposition 2, (42)

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Programs

set_option autoImplicit false

namespace PlatformToken.SmallCost

/-- **Proposition 2** (Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 11, Proposition 2, (42)).

For sufficiently small capacity cost, that is, when `K ∈ [0, ε]`, the blockchain-based business
model strictly dominates the traditional one, `Π^B > Π^$`, unless the venture is unfeasible,
`Π^B = Π^$ = 0`. Only `K` varies; all other parameters are fixed.

**Formalization Note.**
* `Π^$`, `Π^B` are `PiTrad`, `PiBlock`: Lemma 2's and Lemma 3's programs, with the outside
  option `0` (see `Def_PlatformToken_SmallCost_Programs`).
* `K` ranges over `(0, ε]`, not the printed `[0, ε]`: at `K = 0` the two Corollary 1 payoff
  programs coincide on the branch `c ≤ d - s` (e.g. `c = 0`, `m = 1`), contrary to the printed
  strict claim. Lemma 2's literal `(20)` requires `0 < α`, so its program does not represent
  that zero-investment boundary; the paper's proof itself treats `K ∈ (0, ε)` (p. 19).
* The hypothesis `0 < c ∨ 0 < m` is added: with `c = m = 0`, `β^$ = β^B` and the blockchain
  program is the traditional one plus the cap (39), so `Π^B ≤ Π^$` (numerically `c = m = 0`,
  `K = 0.05` gives `Π^$ ≈ 9.69 > Π^B ≈ 5.09`).
* The conclusion also asserts that both objective images are bounded above, so that the
  `sSup`s in `PiTrad`, `PiBlock` are genuine suprema rather than Lean's junk value `0`.
-/
theorem proposition_2 (p : Params) (hp : p.Standing) (hcm : 0 < p.c ∨ 0 < p.m) :
    ∃ ε > 0, ∀ K ∈ Set.Ioc 0 ε,
      BddAbove ((fun x : ℝ × ℝ × ℝ => obj (withK p K) x.2.2 x.1) '' TradFeasible (withK p K)) ∧
      BddAbove ((fun x : ℝ × ℝ × ℝ => obj (withK p K) x.2.2 x.1) '' BlockFeasible (withK p K)) ∧
      (PiTrad (withK p K) < PiBlock (withK p K) ∨
        (PiBlock (withK p K) = 0 ∧ PiTrad (withK p K) = 0)) := by sorry

end PlatformToken.SmallCost
