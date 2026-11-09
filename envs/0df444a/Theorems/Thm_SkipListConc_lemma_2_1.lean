-- Prove2me | Theorems.Thm_SkipListConc_lemma_2_1
-- name    : SkipListConc.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:06.982119+00:00
-- url     : https://prove2.me/theorems/4441ca36-37ce-444d-98ae-3739456af81e
-- title:
--   Lemma 2.1 — uniform crossing tail $\Pr[H_x(j+1)\ge\ell\mid H_x(j)=c]\le p^{\ell-K}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   For every item $x$ and every level $\ell\ge1$:
--
--   1. $\Pr[H_x(1)\ge\ell]\le p^{\ell-K}$;
--   2. for every $j\ge1$ and every source height $c$ with $1\le c<\ell$, one update satisfies
--   $$
--   \Pr\bigl[H_x(j+1)\ge\ell\ \big|\ H_x(j)=c\bigr]\ \le\ p^{\ell-K}.
--   $$
--
--   The bound is uniform in the source height and the operation index; a union bound over updates gives the height upper tail (T1).
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: conditional probability Pr[· | B] → ProbabilityTheory.cond P B, the zero measure when Pr[B] = 0; reason: an upper bound on a conditional probability says nothing when the conditioning event is null
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 2.1, p.13

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_height

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 2.1 (uniform crossing tail) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Lemma 2.1, p.13).
For every level `ℓ ≥ 1`: (i) `Pr[H_x(1) ≥ ℓ] ≤ p^{ℓ−K}`; (ii) for every `j ≥ 1` and every source
height `c` with `1 ≤ c < ℓ`, `Pr[H_x(j+1) ≥ ℓ | H_x(j) = c] ≤ p^{ℓ−K}`.

**Formalization Note** `p^{ℓ−K}` is an integer power (`≥ 1` when `ℓ ≤ K`). The conditional
probability is `ProbabilityTheory.cond`, which is the zero measure when `Pr[H_x(j) = c] = 0`. -/
theorem lemma_2_1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (hξ : IsPromotionNoise p K μJ P ξ) (x : α)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    P {ω | ℓ ≤ height p ξ x 1 ω} ≤ ENNReal.ofReal (p ^ ((ℓ : ℤ) - K)) ∧
      ∀ j c : ℕ, 1 ≤ j → 1 ≤ c → c < ℓ →
        ProbabilityTheory.cond P {ω | height p ξ x j ω = c} {ω | ℓ ≤ height p ξ x (j + 1) ω} ≤
          ENNReal.ofReal (p ^ ((ℓ : ℤ) - K)) := by sorry

end SkipListConc
