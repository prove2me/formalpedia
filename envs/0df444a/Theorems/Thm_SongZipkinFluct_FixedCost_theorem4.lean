-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem4
-- name    : SongZipkinFluct.FixedCost.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:11.25613+00:00
-- url     : https://prove2.me/theorems/78880dc2-f3a7-4825-9f63-1c2b03f35b9a
-- title:
--   Theorem 4 — y*(i) ≤ S*_n(i) < S⁺(i) and r⁻⁻(i) ≤ r⁻(i) ≤ r*_n(i) ≤ r⁺(i) for all n ≥ 1
-- statement:
--   In the fixed-cost model (standing hypotheses, $\alpha\bar c < p$, $K > 0$, $W_0 = W_\infty$ of the linear model), let $y^+(i)$ be the smallest minimizer of $G^+(i,\cdot)$, $y^+_{\min} = \min_i y^+(i)$, and $y^*(i)$ the smallest minimizer of $G_0(i,\cdot)$. Then the bounds $S^+(i)$, $r^+(i)$, $r^-(i)$, $r^{--}(i)$ of p. 358 exist, and for all $n \ge 1$ and $i \in I$, with $S^*_n(i)$, $r^*_n(i)$ the parameters of Theorem 3(b):
--   $$
--   y^*(i) \le S^*_n(i) < S^+(i),
--   $$
--   $$
--   r^{--}(i) \le r^-(i) \le r^*_n(i) \le r^+(i).
--   $$
--
--   These bounds, of the type Veinott (1966) gave for discrete-time models without a world variable, localize the optimal $n$-stage parameters in a box computed from the myopic cost $G^+$ and the linear model alone, uniformly in $n$.
--
--   **Formalization Note** The existence of $S^+$, $r^+$, $r^-$, $r^{--}$, taken for granted in the paper when it defines them, is part of the conclusion; $y^+$, $y^+_{\min}$, $y^*$, $S^*_n$, $r^*_n$ are taken through their defining properties.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 358, Theorem 4 (proof p. 368)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 4 (p. 358; proof p. 368) of Song and Zipkin (1993). Fixed-cost model of §3.2
(`K = K̄F̃_L(α) > 0`, `W₀ = W_∞`, `G₀ = G_∞` of the linear model). Let `y⁺(i)` be the smallest
minimizer of `G⁺(i, ·)`, `y⁺_min = min_i y⁺(i)`, `y*(i)` the smallest minimizer of `G₀(i, ·)`.
Then the bounds of p. 358,

* `S⁺(i) = min{y ≥ y⁺(i) : G⁺(i, y) − G⁺(i, y⁺(i)) > γK}`,
* `r⁺(i) = max{y < y⁺(i) : G⁺(i, y) − G⁺(i, y⁺(i)) > (1 − γ)K}`,
* `r⁻(i) = max{y < y*(i) : G₀(i, y) − G₀(i, y*(i)) > K}`,
* `r⁻⁻(i) = max{y < y⁺_min : G⁺(i, y) − G⁺(i, y⁺_min) > K}`,

exist, and for all `n ≥ 1` and `i ∈ I`, with `S*_n(i)`, `r*_n(i)` as in Theorem 3(b):

* (a) `y*(i) ≤ S*_n(i) < S⁺(i)`;
* (b) `r⁻⁻(i) ≤ r⁻(i) ≤ r*_n(i) ≤ r⁺(i)`.

Formalization Note: every minimizer and extremal integer is taken through its defining property
(`IsLeast`/`IsGreatest`), never through `sInf`/`sSup` on `ℤ`. The existence of `S⁺`, `r⁺`,
`r⁻`, `r⁻⁻`, which the paper takes for granted when it defines them, is part of the
conclusion. -/
theorem theorem4 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar)
    (yplus : I → ℤ) (hyplus : IsYPlus M yplus) (ymin : ℤ) (hymin : IsYPlusMin yplus ymin)
    (ystar : I → ℤ) (hystar : IsYStar M ystar) :
    ((∃ Splus, IsSPlus M yplus Splus) ∧ (∃ rplus, IsRPlus M yplus rplus) ∧
        (∃ rminus, IsRMinus M ystar rminus) ∧ (∃ rmm, IsRMinusMinus M ymin rmm)) ∧
      ∀ (Splus rplus rminus rmm : I → ℤ) (rs Ss : ℕ → I → ℤ),
        IsSPlus M yplus Splus → IsRPlus M yplus rplus → IsRMinus M ystar rminus →
        IsRMinusMinus M ymin rmm → IsStageParams M rs Ss →
        ∀ n : ℕ, 1 ≤ n → ∀ i : I,
          (ystar i ≤ Ss n i ∧ Ss n i < Splus i) ∧
          (rmm i ≤ rminus i ∧ rminus i ≤ rs n i ∧ rs n i ≤ rplus i) := by sorry

end SongZipkinFluct.FixedCost
