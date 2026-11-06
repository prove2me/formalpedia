-- Prove2me | Theorems.Thm_UnobservedWelfare_theorem_3_1
-- name    : UnobservedWelfare.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:28.741789+00:00
-- url     : https://prove2.me/theorems/435c08ca-fd55-42f5-9697-b01e15c8c229
-- title:
--   Theorem 3.1 — logarithmic welfare regret $\mathbb E[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T]\le KmW[1+\log(T+1)]$
-- statement:
--   There is a numerical constant $K$ such that, for every pair of positive integers $m,T$, every $W>0$ and every admissible production cost $c$, there is a measurable pricing and production policy that uses only $m,T,W,c$ and past prices and purchases, with the following property. For every i.i.d. buyer model on a standard Borel type space satisfying RC at scale $W$ (Definition 2.1), and every permitted demand selection, the policy fulfills all purchases in full, satisfies $I_t\ge0$ on every path for every $t\in[T]$, and
--   $$0\le\mathbb E\big[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T\big]\le KmW\,[1+\log(T+1)].$$
--   The constant $K$ is independent of $m,T,W$, the type distribution and $c$; the policy does not use the type distribution, whose support may be infinite.
--
--   This is the main result of the paper: a seller who observes only purchases achieves welfare regret logarithmic in the horizon against an offline planner that knows every realized type.
--
--   **Formalization Note** $K$ is quantified first and the policy before the buyer model, the probability space and the demand selection. Type spaces and probability spaces are in `Type`.
--
--   Differences from the source:
--   - generalization: "there is a measurable pricing and production policy" (purchase-based policies may use their own random choices) → there is a deterministic `Policy m` that is measurable and outputs $q_t\in[0,1]^m$, $p_t\gg0$ on every history; reason: a deterministic policy is a purchase-based policy, so the Lean statement implies the source one
--   - generalization: $0\le\mathbb E[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T]$ → $0\le\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T$ on every path; reason: the pathwise inequality implies the expectation one (Lemma A.1, p.43, proves it pathwise)
--   - encoding: $\mathbb E[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T]$ → `expectedRegret`: the outer integral of the gap mapped to $[0,\infty]$; reason: the gap is nonnegative, and the outer integral equals the expectation whenever the gap is measurable
--   - encoding: "every permitted demand selection" (selections measurable in the current type, the past and the seed, App. C.2) → an `Execution`: $X_t$ is $\mathcal F_t$-measurable and lies in $D_{\theta_t}(p_t)$ on every path; reason: this is the source formalization of App. C.2
--   - encoding: "a numerical constant $K$" → $\exists K>0$; reason: increasing $K$ preserves the bound
--   - encoding: standard Borel type space; a probability space → `Θ Ω : Type`; reason: universe convention; every instance of the source lives in `Type`
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Theorem 3.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Theorem 3.1 (Logarithmic welfare regret)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Theorem 3.1, p.20 (PDF p.22)).
There is a numerical constant `K` such that for all positive integers `m, T`, every `W > 0` and
every admissible production cost `c`, some measurable pricing and production policy, using only
`m, T, W, c` and past prices and purchases, satisfies: for every i.i.d. buyer model satisfying RC at
scale `W` and every permitted demand selection, the policy fulfills all purchases in full with
`I_t ≥ 0` on every path for every `t ∈ [T]`, and `0 ≤ E[OPT^agg_T − ALG_T] ≤ KmW[1 + log(T + 1)]`.

**Formalization Note** The quantifiers are in the paper's order: `K` first, the policy after
`m, T, W, c` and before the type space, distribution, utilities, probability space and demand
selection. A `Policy m` sees only the past `(p_j, X_j)`, so it cannot use the type distribution.
The policy is deterministic (the paper allows randomized ones; a deterministic witness is a
special case). Type and probability spaces live in `Type`. `0 ≤ OPT − ALG` is stated on every path,
which implies it in expectation; the expectation is `Execution.expectedRegret` (outer integral of
the nonnegative gap). -/
theorem theorem_3_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ (m T : ℕ), 1 ≤ m → 1 ≤ T → ∀ W : ℝ, 0 < W →
      ∀ c : (Fin m → ℝ) → ℝ, IsAdmissibleCost c →
      ∃ π : Policy m, IsPurchasePolicy π ∧
      ∀ (Θ : Type) [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ)
        [IsProbabilityMeasure P] (u : Θ → (Fin m → ℝ) → EReal),
        IsBuyerModel u → (∀ θ, IsRC W (u θ)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Execution m T P u μ), E.DrivenBy π →
        E.IsSafe ∧ (∀ ω, 0 ≤ E.OPTagg c ω - E.ALG c ω) ∧
        E.expectedRegret c ≤ ENNReal.ofReal (K * m * W * (1 + Real.log ((T : ℝ) + 1))) := by sorry

end UnobservedWelfare
