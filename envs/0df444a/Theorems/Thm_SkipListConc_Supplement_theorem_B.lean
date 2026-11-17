-- Prove2me | Theorems.Thm_SkipListConc_Supplement_theorem_B
-- name    : SkipListConc.Supplement.theorem_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:01:58.490197+00:00
-- url     : https://prove2.me/theorems/8633a7ae-1ed2-4c0f-92e7-74e99059816c
-- title:
--   Theorem B — multiplicative sequence bound $O_{p,K}(A(\sigma)(1+\log\frac1\delta))$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge1$ is an integer, operation sequences are fixed in advance, and heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law, never redrawn.
--
--   There is a constant $C=C(p,K)>0$ such that for every key set, every operation sequence $\sigma$ of length $F$, every probability space carrying the randomness of Definition 1.1 and every $0<\delta<1$, each of the following holds with probability at least $1-\delta$:
--   $$
--   \sum_{t=1}^{F}\mathrm{cost}_t(x_t)\le C\,A(\sigma)\Bigl(1+\log\frac1\delta\Bigr),\qquad
--   \sum_{t=1}^{F}\mathrm{cost}_t(x_t)\le C\,\mathrm{Ent}(\sigma)\Bigl(1+\log\frac1\delta\Bigr),
--   $$
--   where $A(\sigma)=\sum_ta_t$ and $\mathrm{Ent}(\sigma)=F+\sum_xf_x\log_b(F/f_x)$.
--
--   This is the multiplicative sequence bound: the costs of different charges are dependent, and the confidence factor $1+\log(1/\delta)$ multiplies the whole benchmark.
--
--   Differences from the source:
--   - encoding: Definition 1.1 with fresh, independent gate, jump and geometric variables → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); reason: the published model of the base mission; realizes the transition probabilities (1)
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type; reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
--   - encoding: "with probability at least 1 − δ, X ≤ B" → P{X > B} ≤ δ; reason: complement
--   - encoding: O_{p,K}(·), constants depending only on p and K (p.7) → ∃ C > 0 chosen after p, K and before the key type, σ, the jump law, the probability space and every remaining parameter; reason: the source's definition of O_{p,K}
--   - encoding: the A(σ) form and the Ent(σ) form, each = O_{p,K}(·) → both with one constant C; reason: taking the larger constant is equivalent
--   - encoding: log(1/δ) → natural logarithm; reason: the base only changes the constant
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem B, p.8

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_totalCost
import Definitions.Def_SkipListConc_entropy
import Definitions.Def_SkipListConc_Supplement_benchSum

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- Theorem B (multiplicative sequence bound) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem B, p.8). For every operation
sequence `σ` and every `0 < δ < 1`, with probability at least `1 − δ`,
`∑_t cost_t(x_t) = O_{p,K}(A(σ)(1 + log(1/δ))) = O_{p,K}(Ent(σ)(1 + log(1/δ)))`.

**Formalization Note** One constant `C > 0` depending only on `p` and `K` serves both forms. "With probability at least `1 − δ`, `X ≤ B`" is `Pr[X > B] ≤ δ`; `log` is the natural logarithm.
The heights follow Definition 1.1 without reseeding. -/
theorem theorem_B (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
          P {ω | C * (benchSum p σ * (1 + Real.log (1 / δ))) < (totalCost p ξ σ ω : ℝ)} ≤
              ENNReal.ofReal δ ∧
            P {ω | C * (entropy p σ * (1 + Real.log (1 / δ))) < (totalCost p ξ σ ω : ℝ)} ≤
              ENNReal.ofReal δ := by sorry

end SkipListConc.Supplement
