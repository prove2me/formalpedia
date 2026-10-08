-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem5e_theorem6
-- name    : SongZipkinFluct.FixedCost.theorem5e_theorem6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:25.492293+00:00
-- url     : https://prove2.me/theorems/200f25e3-5377-424b-846f-937f22d57bd3
-- title:
--   Theorems 5(e) and 6 — the world-dependent (r*, S*) policy is optimal, with y* ≤ S* < S⁺ and r⁻⁻ ≤ r⁻ ≤ r* ≤ r⁺
-- statement:
--   Consider the fixed-cost model: the standing hypotheses, Assumption 1 ($\alpha\bar c < p$), a positive fixed cost $\bar K > 0$ (so $K = \bar K\tilde F_L(\alpha) > 0$), and the terminal cost $W_0 = W_\infty$ of the linear order-cost model. Then:
--
--   1. **(Existence.)** The quantities the paper defines exist: the smallest minimizer $y^+(i)$ of $G^+(i,\cdot)$, $y^+_{\min} = \min_i y^+(i)$, the smallest minimizer $y^*(i)$ of $G_0(i, \cdot)$, the bounds $S^+(i)$, $r^+(i)$, $r^-(i)$, $r^{--}(i)$ of p. 358, and the $n$-stage parameters $S^*_n(i)$, $r^*_n(i)$ of Theorem 3(b) for all $n \ge 1$.
--   2. For any such quantities, for every $i$ the sequence $\{(r^*_n(i), S^*_n(i))\}_n$ has a limit point; and whenever $(r^*(i), S^*(i))$ is a limit point for every $i$:
--      * **(Theorem 5(e))** the world-dependent $(r, S)$ policy with parameters $\{(r^*(i), S^*(i))\}_{i\in I}$ — order up to $S^*(i)$ if the inventory position is at most $r^*(i)$ while the world is in state $i$, and do not order otherwise — is optimal for the infinite-horizon problem: from every initial state its expected total discounted cost is at most that of any feasible policy;
--      * **(Theorem 6)** for all $i$,
--      $$
--      y^*(i) \le S^*(i) < S^+(i),\qquad r^{--}(i) \le r^-(i) \le r^*(i) \le r^+(i).
--      $$
--
--   The theorem shows that, even with a Markov-modulated demand rate and stochastic lead times, a stationary $(r, S)$ policy whose parameters depend only on the current state of the world is optimal, and that its parameters lie in a box computed from the myopic cost and the linear model.
--
--   **Formalization Note** Policies are deterministic and may depend on the whole history; costs are valued in $[0, \infty]$. A limit point of the integer sequence is a pair taken for infinitely many $n$. Every minimizer and extremal integer is taken through its defining property; the existence clause ensures these hypotheses can be met.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 359, Theorem 5(e) and Theorem 6

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds
import Definitions.Def_SongZipkinFluct_FixedCost_Policy

open Filter

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 5(e) together with Theorem 6 (p. 359) of Song and Zipkin, *Inventory Control in a
Fluctuating Demand Environment*, Oper. Res. 41(2):351–370 (1993). Fixed-cost model of §3.2:
standing hypotheses, Assumption 1 (`αc̄ < p`), `K̄ > 0` (so `K = K̄F̃_L(α) > 0`), terminal cost
`W₀ = W_∞` of the linear model.

1. (Existence.) The parameters the paper defines exist: `y⁺(i)` (smallest minimizer of
   `G⁺(i, ·)`), `y⁺_min = min_i y⁺(i)`, `y*(i)` (smallest minimizer of `G₀(i, ·)`), the bounds
   `S⁺`, `r⁺`, `r⁻`, `r⁻⁻` of p. 358, and the `n`-stage parameters `S*_n(i)`, `r*_n(i)` of
   Theorem 3(b) for all `n ≥ 1`.
2. For any such parameters: for every `i` the sequence `n ↦ (r*_n(i), S*_n(i))` has a limit
   point, and for any `r*, S* : I → ℤ` such that each `(r*(i), S*(i))` is a limit point,
   * (Theorem 5(e)) the world-dependent `(r, S)` policy with parameters `{(r*(i), S*(i))}`
     (order up to `S*(i)` iff the inventory position is `≤ r*(i)`) is optimal for the
     infinite-horizon problem (1) with fixed cost `K`, among all feasible deterministic
     history-dependent policies and from every initial state;
   * (Theorem 6) `y*(i) ≤ S*(i) < S⁺(i)` and `r⁻⁻(i) ≤ r⁻(i) ≤ r*(i) ≤ r⁺(i)` for all `i`.

Formalization Note: a limit point of the integer sequence is a value taken infinitely often.
All minimizers and extremal integers are taken through their defining properties; the existence
conjunct makes the hypotheses of part 2 satisfiable. -/
theorem theorem5e_theorem6 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) :
    ((∃ yplus, IsYPlus M yplus) ∧
      (∀ yplus, IsYPlus M yplus → ∃ ymin, IsYPlusMin yplus ymin) ∧
      (∃ ystar, IsYStar M ystar) ∧
      (∀ yplus, IsYPlus M yplus →
        (∃ Splus, IsSPlus M yplus Splus) ∧ (∃ rplus, IsRPlus M yplus rplus)) ∧
      (∀ ystar, IsYStar M ystar → ∃ rminus, IsRMinus M ystar rminus) ∧
      (∀ yplus ymin, IsYPlus M yplus → IsYPlusMin yplus ymin →
        ∃ rmm, IsRMinusMinus M ymin rmm) ∧
      (∃ rs Ss, IsStageParams M rs Ss)) ∧
    ∀ (yplus : I → ℤ) (ymin : ℤ) (ystar Splus rplus rminus rmm : I → ℤ)
      (rs Ss : ℕ → I → ℤ),
      IsYPlus M yplus → IsYPlusMin yplus ymin → IsYStar M ystar →
      IsSPlus M yplus Splus → IsRPlus M yplus rplus → IsRMinus M ystar rminus →
      IsRMinusMinus M ymin rmm → IsStageParams M rs Ss →
      (∀ i, ∃ r S : ℤ, ∃ᶠ n in atTop, rs n i = r ∧ Ss n i = S) ∧
      ∀ rstar Sstar : I → ℤ,
        (∀ i, ∃ᶠ n in atTop, rs n i = rstar i ∧ Ss n i = Sstar i) →
        IsOptimal M M.K (rSPolicy rstar Sstar) ∧
        ∀ i, (ystar i ≤ Sstar i ∧ Sstar i < Splus i) ∧
          (rmm i ≤ rminus i ∧ rminus i ≤ rstar i ∧ rstar i ≤ rplus i) := by sorry

end SongZipkinFluct.FixedCost
