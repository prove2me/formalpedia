-- Prove2me | Theorems.Thm_SkipListConc_lemma_2_2
-- name    : SkipListConc.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:52.35862+00:00
-- url     : https://prove2.me/theorems/4aaf977c-8715-4d1b-82f1-57258e9c9156
-- title:
--   Lemma 2.2 — height upper tail $\Pr[H_x(j)\ge\ell]\le j\,p^{\ell-K}$ (T1)
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   For every item $x$, every $j\ge1$ and every level $\ell\ge1$,
--   $$
--   \Pr[H_x(j)\ge \ell]\ \le\ j\,p^{\ell-K}.
--   $$
--   Consequently, for every real $a\ge0$,
--   $$
--   \Pr\bigl[H_x(j)\ge K+\log_b j+a\bigr]\ \le\ p^{a}.
--   $$
--
--   This is property (T1): after $j$ operations the height exceeds $\log_b j$ by more than $K+a$ only with geometrically small probability.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 2.2, p.14

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_height

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 2.2 (height upper tail, property (T1)) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 2.2, p.14). For every `j ≥ 1` and every level `ℓ ≥ 1`, `Pr[H_x(j) ≥ ℓ] ≤ j p^{ℓ−K}`.
Consequently, for every real `a ≥ 0`, `Pr[H_x(j) ≥ K + log_b j + a] ≤ p^a`, `b = 1/p`.

**Formalization Note** `p^{ℓ−K}` is an integer power, `p^a` a real power. -/
theorem lemma_2_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (hξ : IsPromotionNoise p K μJ P ξ) (x : α) :
    (∀ j ℓ : ℕ, 1 ≤ j → 1 ≤ ℓ →
        P {ω | ℓ ≤ height p ξ x j ω} ≤ ENNReal.ofReal ((j : ℝ) * p ^ ((ℓ : ℤ) - K))) ∧
      ∀ j : ℕ, 1 ≤ j → ∀ a : ℝ, 0 ≤ a →
        P {ω | (K : ℝ) + Real.logb (1 / p) (j : ℝ) + a ≤ (height p ξ x j ω : ℝ)} ≤
          ENNReal.ofReal (p ^ a) := by sorry

end SkipListConc
