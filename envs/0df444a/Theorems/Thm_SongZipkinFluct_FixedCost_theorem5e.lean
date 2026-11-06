-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem5e
-- name    : SongZipkinFluct.FixedCost.theorem5e
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T05:51:24.81642+00:00
-- url     : https://prove2.me/theorems/ddde47e4-abb3-45fa-b985-38764c610d1a
-- title:
--   Theorem 5(e) — every limit point $(r^*(i),S^*(i))$ of the $n$-stage parameters gives an optimal world-dependent $(r,S)$ policy
-- statement:
--   Fixed-cost model of §3.2: standing hypotheses, Assumption 1 ($\alpha\bar c < p$), $\bar K>0$ so that $K = \bar K\tilde F_L(\alpha) > 0$, and terminal cost $W_0 = W_\infty$ of the linear model. For $n\ge1$ let $S^*_n(i)$ be the smallest minimizer of $G_n(i,\cdot)$ and $r^*_n(i)$ the largest $y < S^*_n(i)$ with $G_n(i,y) > K + G_n(i,S^*_n(i))$ (Theorem 3(b)).
--
--   **Claim (Theorem 5(e)).** Let $r^*,S^* : I\to\mathbb Z$ be such that for every $i$ the pair $(r^*(i),S^*(i))$ is a limit point of $\{(r^*_n(i),S^*_n(i))\}_n$, i.e. it equals $(r^*_n(i),S^*_n(i))$ for infinitely many $n$. Then the stationary world-dependent $(r,S)$ policy — when the world is in state $i$ and the inventory position is $x$, order up to $S^*(i)$ if $x\le r^*(i)$ and do not order otherwise — is optimal for the infinite-horizon discounted problem (1) with fixed cost $K$: it is feasible, and from every initial state $(i,x)$ its expected total discounted cost is at most that of any feasible deterministic history-dependent policy.
--
--   Policies are deterministic and may depend on the whole history; costs take values in $[0,\infty]$ and the infinite-horizon cost is the supremum of the $N$-epoch costs.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 359, Theorem 5(e)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds
import Definitions.Def_SongZipkinFluct_FixedCost_Policy

open Filter

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 5(e) (p. 359) of Song and Zipkin (1993). Fixed-cost model of §3.2
(`K = K̄F̃_L(α) > 0`, `W₀ = W_∞` of the linear model). Let `S*_n(i)`, `r*_n(i)` (`n ≥ 1`) be the
parameters of Theorem 3(b). If, for every `i`, `(r*(i), S*(i))` is a limit point of
`n ↦ (r*_n(i), S*_n(i))` (a pair taken for infinitely many `n`), then the world-dependent
`(r, S)` policy with parameters `{(r*(i), S*(i))}` is optimal for the infinite-horizon
problem (1) with fixed cost `K`, among all feasible deterministic history-dependent policies and
from every initial state. -/
theorem theorem5e {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar)
    (rs Ss : ℕ → I → ℤ) (hrs : IsStageParams M rs Ss) (rstar Sstar : I → ℤ)
    (hlim : ∀ i, ∃ᶠ n in atTop, rs n i = rstar i ∧ Ss n i = Sstar i) :
    IsOptimal M M.K (rSPolicy rstar Sstar) := by
  sorry

end SongZipkinFluct.FixedCost
