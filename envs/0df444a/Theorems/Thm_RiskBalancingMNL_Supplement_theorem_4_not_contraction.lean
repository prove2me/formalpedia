-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_theorem_4_not_contraction
-- name    : RiskBalancingMNL.Supplement.theorem_4_not_contraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:59:30.175723+00:00
-- url     : https://prove2.me/theorems/e4d52ded-d152-5538-b18f-20cb328b779b
-- title:
--   Theorem 4 (corrected: false as printed; $f$ is not a contraction on $[0,\pi^o]$ for $\lambda\in(0,\bar\lambda)$) — the fixed-point map of (27)
-- statement:
--   Theorem 4 of the paper states that the fixed-point map $f$ of (27) is a contraction mapping on $[0,\pi^o]$, where $\pi^o$ is the profit-maximizing profit. This is false; the statement here is its refutation.
--
--   Consider the MNL model with asymmetric price sensitivities $\hat b_i>0$ and at least one product, let $A=\sum_ie^{\hat a_i-\hat b_ic_i}$ and $\bar\lambda=A/(1+A)$, and let $\lambda\in(0,\bar\lambda)$. With $f(\pi)=\sum_im_i(\pi,\theta(\pi))q_i(\pi,\theta(\pi))$ as in (27):
--   1. $f(0)=0$;
--   2. $\pi^o>0$;
--   3. there is no $k<1$ such that
--   $$
--   |f(x)-f(y)|\le k\,|x-y|\qquad\text{for all }x,y\in[0,\pi^o].
--   $$
--   So $f$ is not a contraction on $[0,\pi^o]$ under any reading of the term (with or without $f([0,\pi^o])\subseteq[0,\pi^o]$). The reason is the slope at the origin: $f(\pi)/\pi\to\bar\lambda/\lambda>1$ as $\pi\to0^+$. Moreover $f$ has the second fixed point $\pi^*$, the optimal profit, so the bisection the paper proposes must avoid the trivial fixed point $0$.
--
--   Differences from the source:
--   - correction: f(π) is a contraction mapping on [0, π°] → for n ≥ 1 and every λ ∈ (0, λ̄): f(0) = 0, π° > 0, and no k < 1 satisfies |f(x) − f(y)| ≤ k|x − y| on [0, π°]; reason: f(0) = 0 (θ(0) = 0 and all markups (24) vanish) and f(π)/π → λ̄/λ > 1 as π → 0⁺, since θ(π) ≈ (π/λ)²/(1 + A) and m_j(π, θ(π)) ≈ π/λ; numerically, on random instances, f(10⁻⁵)/10⁻⁵ agrees with λ̄/λ to 10⁻⁵
--   - encoding: π° the profit-maximizing profit → sSup of π(m) over all m ∈ ℝⁿ; reason: for n ≥ 1 the profit is bounded above and the supremum is attained, so it is the optimal profit at λ = 0
--   - encoding: θ(π) the unique root of ζ → thetaOf: the witness of ∃! θ ≥ 0, ζ(θ) = 0; reason: the companion claim zeta_unique_root shows the root exists and is unique
--   - encoding: primitives a_i, y_i, b, β of (16) → reduced form â_i, b̂_i > 0, c_i; reason: the primitives enter only through â_i = a_i + y_i and b̂_i = b − βy_i, and every positive b̂ arises
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.2, Theorem 4, p.19; $f$ (27), p.18; $\pi^o$, p.19

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_zeta

namespace RiskBalancingMNL.Supplement

/-- **Theorem 4 (Contraction Mapping of the Fixed-point Relation) is false as printed**, Li &
Webster, *Optimizing Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of
2021-11-14), p.19: "`f(π)` is a contraction mapping on `[0, π°]`", with `f` the fixed-point map
(27) of p.18 and `π°` the profit-maximizing profit.

Refutation: for every asymmetric MNL model with at least one product and every
`λ ∈ (0, λ̄)`, `λ̄ = A/(1 + A)`, `A = Σᵢ e^{âᵢ − b̂ᵢcᵢ}`:
1. `f(0) = 0`;
2. `π° > 0`;
3. there is no `k < 1` with `|f(x) − f(y)| ≤ k|x − y|` for all `x, y ∈ [0, π°]`.

**Formalization Note** The third clause excludes every reading of "contraction mapping" (a
Lipschitz constant below `1`, with or without `f([0, π°]) ⊆ [0, π°]`). The reason is
`f(π)/π → λ̄/λ > 1` as `π → 0⁺`. `π°` is `sSup` of the profit over `ℝⁿ` (`piO`). -/
theorem theorem_4_not_contraction {n : ℕ} [NeZero n] (P : AsymParams n) (lam : ℝ)
    (hlam0 : 0 < lam) (hlam : lam < P.lamBar) :
    fixedPointMap P lam 0 = 0 ∧ 0 < piO P ∧
    ¬ ∃ k : ℝ, k < 1 ∧ ∀ x ∈ Set.Icc 0 (piO P), ∀ y ∈ Set.Icc 0 (piO P),
      |fixedPointMap P lam x - fixedPointMap P lam y| ≤ k * |x - y| := by sorry

end RiskBalancingMNL.Supplement
