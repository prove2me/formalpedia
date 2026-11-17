-- Prove2me | Theorems.Thm_SkipListConc_Supplement_theorem_A
-- name    : SkipListConc.Supplement.theorem_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:01:08.059036+00:00
-- url     : https://prove2.me/theorems/7bf59f26-44dd-4360-8d0a-dbacf726d722
-- title:
--   Theorem A — tail bound for one search: $\Pr[\mathrm{cost}_t(x_t)>C(a_t+u)]\le3e^{-u}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge1$ is an integer, operation sequences are fixed in advance, and heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law, never redrawn. Let $\mathrm{cost}_t(x_t)$ be the cost of the search of the charge at time $t$, and $a_t=1+\log_b(t/f_t)$ its benchmark cost.
--
--   There is a constant $C=C(p,K)>0$ such that for every key set, every operation sequence $\sigma$, every probability space carrying the randomness of Definition 1.1 and every charge $t$ (insertions included):
--
--   1. for every $u\ge0$,
--   $$
--   \Pr\bigl[\mathrm{cost}_t(x_t)>C(a_t+u)\bigr]\le 3e^{-u};
--   $$
--   2. for every $0<\delta<1$, with probability at least $1-\delta$,
--   $$
--   \mathrm{cost}_t(x_t)\le C\Bigl(1+\log_b\frac{t}{f_t}+\log\frac1\delta\Bigr).
--   $$
--
--   This is the tail bound for one search: the cost of a single charge exceeds its benchmark cost by more than $u$ units only with exponentially small probability.
--
--   Differences from the source:
--   - encoding: Definition 1.1 with fresh, independent gate, jump and geometric variables → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); reason: the published model of the base mission; realizes the transition probabilities (1)
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type; reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
--   - encoding: "with probability at least 1 − δ, X ≤ B" → P{X > B} ≤ δ; reason: complement
--   - encoding: O_{p,K}(·), constants depending only on p and K (p.7) → ∃ C > 0 chosen after p, K and before the key type, σ, the jump law, the probability space and every remaining parameter; reason: the source's definition of O_{p,K}
--   - encoding: the δ-form and the "equivalently" u-form, each with an O_{p,K} constant → both forms with one constant C; reason: each form implies the other with a larger constant, so one common constant is equivalent
--   - encoding: log(1/δ) → natural logarithm; reason: the base only changes the constant
--   - encoding: times t = 1, …, F; f_t = f_{x_t}(t) → 0-based positions t; t + 1 operations so far; f_t = opCount σ x_t t + 1; reason: index shift only
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem A, p.7

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_Supplement_chargeBench
import Definitions.Def_SkipListConc_Supplement_chargeCost

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- Theorem A (tail bound for one search) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem A, p.7). For every charge `t` and
every `0 < δ < 1`, with probability at least `1 − δ`,
`cost_t(x_t) = O_{p,K}(1 + log_b(t / f_t) + log(1/δ))`. Equivalently, there is a constant
`C_{p,K} > 0` such that `Pr[cost_t(x_t) > C_{p,K}(a_t + u)] ≤ 3e^{−u}` for every charge `t` and
every `u ≥ 0`.

**Formalization Note** One constant `C > 0`, depending only on `p` and `K` (chosen before the
key type, `σ`, the jump law, the probability space, `t`, `u` and `δ`), serves both forms. "With probability at least `1 − δ`, `X ≤ B`" is `Pr[X > B] ≤ δ`; `log` is the natural logarithm.
Positions are 0-based (`t + 1` operations so far, `f_t = opCount σ x_t t + 1`); the heights follow
Definition 1.1 without reseeding. -/
theorem theorem_A (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ t : Fin σ.length,
          (∀ u : ℝ, 0 ≤ u →
            P {ω | C * (chargeBench p σ t + u) < (chargeCost p ξ σ t ω : ℝ)} ≤
              ENNReal.ofReal (3 * Real.exp (-u))) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 →
            P {ω | C * (1 + Real.logb (1 / p)
                  (((t : ℕ) + 1 : ℝ) / ((opCount σ (σ.get t) t : ℝ) + 1)) + Real.log (1 / δ)) <
                (chargeCost p ξ σ t ω : ℝ)} ≤ ENNReal.ofReal δ := by sorry

end SkipListConc.Supplement
