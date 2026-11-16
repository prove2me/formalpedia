-- Prove2me | Theorems.Thm_UnobservedWelfare_Supplement_theorem_7_1
-- name    : UnobservedWelfare.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:19:40.820037+00:00
-- url     : https://prove2.me/theorems/900f8ade-e7a3-4878-a629-a495abed2b7f
-- title:
--   Theorem 7.1 — without RC, every feasible causal policy has welfare regret $\ge k_0T^{1/4}$
-- statement:
--   There is a one-good market — a standard Borel type space $\Theta$, a type distribution $P$, utilities $u_\theta:\mathbb R_+\to\mathbb R\cup\{-\infty\}$ and a production cost $c$ — such that
--
--   1. $c$ satisfies the cost assumptions of Section 2 (continuous, convex, nondecreasing on $[0,1]$, $c(0)=0$, $c\ge0$);
--   2. every $u_\theta$ satisfies the buyer assumptions of Section 2 (concave, upper semicontinuous, nondecreasing, finite on $(0,\infty)$, jointly measurable) and is continuous on $[0,\infty)$;
--   3. at every price $p>0$ the surplus $S_\theta(p)$ is finite and the demand set $D_\theta(p)$ is nonempty;
--   4. every demanded bundle has expenditure $p\,x\le1$;
--   5. no $u_\theta$ satisfies RC at any scale $W>0$;
--
--   and there are numerical constants $k_0>0$ and $T_0<\infty$ such that, for every $T\ge T_0$ divisible by four, every feasible causal policy satisfies
--
--   $$\mathbb E\big[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T\big]\ \ge\ k_0\,T^{1/4}.$$
--
--   Feasible causal policies may choose production $q_t\in[0,1]$ and allocation $X_t\ge0$ after seeing $\theta_1,\dots,\theta_t$ and independent randomness, may use the type distribution, and must keep the inventory nonnegative.
--
--   The theorem shows that the expenditure bound alone does not yield logarithmic regret: RC (Definition 2.1) cannot be dropped from Theorem 3.1.
--
--   **Formalization Note** The market, $k_0$ and $T_0$ are chosen before $T$, the probability space and the policy. The type space lives in `Type`; the probability space ranges over every universe.
--
--   Differences from the source:
--   - reading: "fail RC at every finite scale" → for every type $\theta$ and every $W>0$, $u_\theta$ fails RC at scale $W$; reason: the stronger of the two readings (a model fails RC iff some utility does); the proof shows every $u_v$ fails
--   - generalization: $\mathbb E[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T]$ → the lower Lebesgue integral `∫⁻` of the gap mapped to $[0,\infty]$; reason: the lower integral is at most any expectation of the gap, so the Lean lower bound implies the source one, and it needs no measurability of $\mathrm{OPT}^{\mathrm{agg}}_T$
--   - encoding: "the assumptions of Section 2" for the utilities → `IsBuyerModel u` (concave, usc, nondecreasing, finite on $\mathbb R_{++}$, jointly measurable); reason: these are the §2 standing assumptions; the source's "continuous, concave, nondecreasing" are included
--   - encoding: "finite attained surplus" → surplus $\ne\pm\infty$ and demand nonempty at every $p>0$; reason: attained means the argmax is nonempty
--   - encoding: "every feasible causal policy" → every `CausalAllocation` with the inventory constraint on every path, on every probability space (any universe); reason: this is the class of p.35
--   - encoding: one good, $T^{1/4}$, "divisible by four" → `Fin 1`, `Real.rpow` with exponent $1/4$, `4 ∣ T`; reason: Lean conventions; same instances
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper's round $t=k+1$; reason: index convention only
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Theorem 7.1, p.34 (PDF p.36); policy class p.35 (PDF p.37)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_Supplement_CausalAllocation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare.Supplement

/-- **Theorem 7.1 (a `T^{1/4}` lower bound without RC)** (Cheng–Tao–Xing, *Maximizing Unobserved
Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Theorem 7.1, p.34
(PDF p.36); policy class p.35 (PDF p.37)).
There is a one-good market — a standard Borel type space `Θ` with a type distribution `P`,
utilities `u θ` and an admissible production cost `c` — whose utilities satisfy the standing
assumptions of §2, are continuous on `ℝ_+`, have finite attained surplus at every price `p > 0`,
induce expenditure `p · x ≤ 1`, and fail RC at every scale `W > 0`; and there are constants
`k₀ > 0`, `T₀` such that for every `T ≥ T₀` divisible by four, every feasible causal policy on
every probability space has `E[OPT^agg_T − ALG_T] ≥ k₀ T^{1/4}`.

**Formalization Note** One good is `Fin 1`. The market, `k₀` and `T₀` are chosen before `T` and the
policy. "Concave, nondecreasing" and the §2 standing assumptions (usc, finite on `ℝ_{++}`, joint
measurability) are `IsBuyerModel u`. "Fail RC at every finite scale" is read per utility. The
policy class is `CausalAllocation` (production and allocation see the current type and independent
randomness; the policy may use `P`) with the inventory constraint on every path. The expectation is
the lower Lebesgue integral `∫⁻` of the gap mapped to `[0, ∞]`; a lower bound on it implies the
lower bound on the expectation. `T^{1/4}` is `Real.rpow`. The type space lives in `Type`; the
policy's probability space ranges over every universe. -/
theorem theorem_7_1 :
    ∃ (Θ : Type) (_ : MeasurableSpace Θ) (_ : StandardBorelSpace Θ) (P : Measure Θ)
      (_ : IsProbabilityMeasure P) (u : Θ → (Fin 1 → ℝ) → EReal) (c : (Fin 1 → ℝ) → ℝ),
      IsAdmissibleCost c ∧ IsBuyerModel u ∧
      (∀ θ, ContinuousOn (u θ) {x | 0 ≤ x}) ∧
      (∀ θ, ∀ p ∈ posOrthant 1, surplus (u θ) p ≠ ⊤ ∧ surplus (u θ) p ≠ ⊥) ∧
      (∀ θ, ∀ p ∈ posOrthant 1, (demand (u θ) p).Nonempty) ∧
      (∀ θ, ∀ p ∈ posOrthant 1, ∀ x ∈ demand (u θ) p, p ⬝ᵥ x ≤ 1) ∧
      (∀ θ, ∀ W : ℝ, 0 < W → ¬ IsRC W (u θ)) ∧
      ∃ k₀ : ℝ, 0 < k₀ ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → 4 ∣ T →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (E : CausalAllocation 1 T P μ), E.IsFeasible →
          ENNReal.ofReal (k₀ * (T : ℝ) ^ (1 / 4 : ℝ)) ≤
            ∫⁻ ω, (E.OPTagg u c ω - E.ALG u c ω).toENNReal ∂μ := by sorry

end UnobservedWelfare.Supplement
