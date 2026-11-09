-- Prove2me | Theorems.Thm_SkipListConc_theorem_C
-- name    : SkipListConc.theorem_C
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:52.816794+00:00
-- url     : https://prove2.me/theorems/6b856755-12ee-492f-bfe3-52d912ae6ed9
-- title:
--   Theorem C — with probability $1-\delta$, $\sum_t\mathrm{cost}_t(x_t)=O_{p,K}(\mathrm{Ent}(\sigma)+F\log(1/\delta))$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   There is a constant $C=C(p,K)>0$ such that for every linearly ordered key set, every operation sequence $\sigma$ of insertions and accesses fixed in advance (of length $F$), every jump law, every probability space carrying the randomness of Definition 1.1, and every $0<\delta<1$, with probability at least $1-\delta$,
--   $$
--   \sum_{t=1}^{F}\mathrm{cost}_t(x_t)\ \le\ C\Bigl(\mathrm{Ent}(\sigma)+F\log\frac1\delta\Bigr),\qquad \mathrm{Ent}(\sigma)=F+\sum_xf_x\log_b\frac F{f_x}.
--   $$
--   Here $\mathrm{cost}_t(x_t)$ is the cost of the search of operation $t$ (levels visited plus steps along levels), in the skip list of the items present, each at its current height, the target at its served height.
--
--   This is the paper's additive sequence bound: the confidence term is added to the benchmark rather than multiplying it, which gives static optimality with probability $1-\delta$ for constant $\delta$.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type (universe 0); reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
--   - encoding: O_{p,K}(·), constants depending only on p and K (p.7) → ∃ C > 0 chosen after p, K and before the key type, σ, the jump law, the probability space and δ; reason: the source's definition of O_{p,K}
--   - encoding: "with probability at least 1 − δ, X ≤ B" → P{X > B} ≤ δ; reason: complement
--   - encoding: log(1/δ) → natural logarithm; reason: the base only changes the constant
--   - encoding: cost of a search: levels visited plus steps along levels → searchCost in closed form ∑_{ℓ = s}^{H_max} (1 + steps on ℓ) over the items present (inserted at or before t), positions 0-based; reason: the source's definition (pp.4–5); checked on Figure 1
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem C, p.8

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_totalCost
import Definitions.Def_SkipListConc_entropy

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Theorem C (additive sequence bound) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Theorem C, p.8).
For every operation sequence `σ` and every `0 < δ < 1`, with probability at least `1 − δ`,
`∑_t cost_t(x_t) = O_{p,K}(Ent(σ) + F log(1/δ))`.

**Formalization Note** `O_{p,K}` is one constant `C > 0` depending only on `p` and `K` (p.7),
chosen before the key type, the sequence, the jump law, the probability space and `δ`. "With
probability at least `1 − δ`, `X ≤ B`" is `Pr[X > B] ≤ δ`. `log` is the natural logarithm. The
heights follow Definition 1.1 (`IsPromotionNoise`), with no reseeding; the cost counts the
searches only. -/
theorem theorem_C (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
          P {ω | C * (entropy p σ + (σ.length : ℝ) * Real.log (1 / δ)) <
              (totalCost p ξ σ ω : ℝ)} ≤ ENNReal.ofReal δ := by sorry

end SkipListConc
