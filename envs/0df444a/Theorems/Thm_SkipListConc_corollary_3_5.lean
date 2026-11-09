-- Prove2me | Theorems.Thm_SkipListConc_corollary_3_5
-- name    : SkipListConc.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:12.729757+00:00
-- url     : https://prove2.me/theorems/4bfe720a-07f9-4015-99e5-accd48a6a228
-- title:
--   Corollary 3.5 — fixed-time hazard $\Pr[H_x(j)\ge\ell+1\mid H_x(j)\ge\ell]\ge p$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   For every item $x$ and every $j\ge1$:
--
--   1. the distribution of $H_x(j)$ is $p$-thick;
--   2. for every level $\ell\ge1$ with $\Pr[H_x(j)\ge\ell]>0$,
--   $$
--   \Pr\bigl[H_x(j)\ge\ell+1\ \big|\ H_x(j)\ge\ell\bigr]\ \ge\ p .
--   $$
--
--   This hazard bound makes the number of horizontal steps on each level of a search at most geometric.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Corollary 3.5, pp.17–18

import Mathlib
import Definitions.Def_SkipListConc_IsThick
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_heightPMF

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Corollary 3.5 (fixed-time hazard) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Corollary 3.5,
pp.17–18). Under Definition 1.1, for every item `x` and every `j ≥ 1` the distribution of
`H_x(j)` is `p`-thick, and for every level `ℓ ≥ 1` with `Pr[H_x(j) ≥ ℓ] > 0`,
`Pr[H_x(j) ≥ ℓ + 1 | H_x(j) ≥ ℓ] ≥ p`. -/
theorem corollary_3_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (hξ : IsPromotionNoise p K μJ P ξ) (x : α)
    (j : ℕ) (hj : 1 ≤ j) :
    IsThick p (heightPMF P p ξ x j) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → P {ω | ℓ ≤ height p ξ x j ω} ≠ 0 →
        ENNReal.ofReal p ≤
          ProbabilityTheory.cond P {ω | ℓ ≤ height p ξ x j ω}
            {ω | ℓ + 1 ≤ height p ξ x j ω} := by sorry

end SkipListConc
