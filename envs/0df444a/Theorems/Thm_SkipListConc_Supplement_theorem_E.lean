-- Prove2me | Theorems.Thm_SkipListConc_Supplement_theorem_E
-- name    : SkipListConc.Supplement.theorem_E
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:03:15.120449+00:00
-- url     : https://prove2.me/theorems/b23294b6-823b-49ec-9234-cc16511c7aeb
-- title:
--   Theorem E — reseeded bound $O_{p,K}(\mathrm{Ent}(\sigma)+n\log\frac1\delta)$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge1$ is an integer, operation sequences are fixed in advance, and heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law, reseeded by Definition 1.6: at the start of each epoch every item present gets a fresh height drawn as at insertion, the list is rebuilt, and the rebuild work is counted.
--
--   1. There is a constant $C=C(p,K)>0$ such that for every key set, every operation sequence $\sigma$ with $n$ distinct items, every probability space carrying fresh randomness for each epoch, and every $0<\delta<1$, with probability at least $1-\delta$,
--   $$
--   \sum_t\mathrm{cost}_t(x_t)+(\text{cost of the rebuilds})\ \le\ C\Bigl(\mathrm{Ent}(\sigma)+n\log\frac1\delta\Bigr).
--   $$
--   2. For every $\kappa>0$ there is $C'=C'(p,K,\kappa)>0$ such that for every such $\sigma$ with $n\ge2$ distinct items, each with $f_x\ge2$, with probability at least $1-n^{-\kappa}$,
--   $$
--   \sum_t\mathrm{cost}_t(x_t)+(\text{cost of the rebuilds})\ \le\ C'\,\mathrm{Ent}(\sigma).
--   $$
--
--   Reseeding limits how long one unusually large height can matter, which replaces the confidence term $F\log(1/\delta)$ of Theorem C by $n\log(1/\delta)$.
--
--   Differences from the source:
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type; reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
--   - encoding: "with probability at least 1 − δ, X ≤ B" → P{X > B} ≤ δ; reason: complement
--   - encoding: Definition 1.6: heights re-initialized at each epoch start, all randomness of an epoch fresh → noise indexed by ((item, epoch), draw) under IsPromotionNoise; heights rsHeight; schedule epochState; reason: realizes Definition 1.6 with independent epochs
--   - reading: the work of the rebuild, O(1 + H_x) per item (p.33) → rebuild cost ∑ over items present of (1 + fresh height) at each epoch start; reason: the source's accounting; constant factors are absorbed by C
--   - encoding: O_{p,K}(·), constants depending only on p and K (p.7) → ∃ C > 0 chosen after p, K and before the key type, σ, the jump law, the probability space and every remaining parameter; reason: the source's definition of O_{p,K}
--   - generalization: first sentence: σ has n distinct items, each with f_x ≥ 2 → first sentence without f_x ≥ 2; reason: the source states (p.5, p.34) that this bound does not use f_x ≥ 2; it specializes to the source's statement
--   - encoding: O_{p,K,κ}(Ent(σ)) for every constant κ > 0 → ∀ κ > 0, ∃ C' > 0 chosen after p, K, κ; reason: the source's definition of the subscripted O
--   - encoding: log(1/δ) → natural logarithm; reason: the base only changes the constant
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem E with Definition 1.6, p.10; proof pp.31–34

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_entropy
import Definitions.Def_SkipListConc_Supplement_reseededCost

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- Theorem E (additive sequence bound with reseeding) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem E, p.10). Let the structure
be reseeded (Definition 1.6), and let `σ` have `n` distinct items, each with `f_x ≥ 2`. For every
`0 < δ < 1`, with probability at least `1 − δ`,
`∑_t cost_t(x_t) + (cost of the rebuilds) = O_{p,K}(Ent(σ) + n log(1/δ))`. Since `f_x ≥ 2` for
every item forces `Ent(σ) ≥ n log_b n`, this cost is `O_{p,K,κ}(Ent(σ))` with probability at least
`1 − n^{−κ}`, for every constant `κ > 0` and `n ≥ 2`.

**Formalization Note** The first sentence is stated without `f_x ≥ 2` (the source notes, p.34,
that its bound does not use it); the second keeps `f_x ≥ 2` and `n ≥ 2`. The first constant
depends on `p, K`, the second on `p, K, κ`. The noise is indexed by `((item, epoch), draw)`
(`rsHeight`), so every epoch's randomness is fresh. "With probability at least `1 − δ`, `X ≤ B`" is `Pr[X > B] ≤ δ`; `log` is the natural logarithm. -/
theorem theorem_E (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
          P {ω | C * (entropy p σ + (σ.toFinset.card : ℝ) * Real.log (1 / δ)) <
              (reseededCost p ξ σ ω : ℝ)} ≤ ENNReal.ofReal δ) ∧
    ∀ κ : ℝ, 0 < κ → ∃ C' : ℝ, 0 < C' ∧
      ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
        (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → 2 ≤ σ.toFinset.card → (∀ x ∈ σ, 2 ≤ σ.count x) →
          P {ω | C' * entropy p σ < (reseededCost p ξ σ ω : ℝ)} ≤
            ENNReal.ofReal ((σ.toFinset.card : ℝ) ^ (-κ)) := by sorry

end SkipListConc.Supplement
