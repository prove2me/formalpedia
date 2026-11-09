-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_11
-- name    : SkipListConc.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:39.563855+00:00
-- url     : https://prove2.me/theorems/51a47832-8ca1-43e7-82c9-de70a01e6f90
-- title:
--   Lemma 4.11 — gap on a search's own level: $\Pr[A_{s_t,t}\ge r]\le(1-p)^{r-1}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   For every operation sequence $\sigma$, every charge $t$ and every integer $r\ge1$,
--   $$
--   \Pr\bigl[A_{s_t,t}\ge r\bigr]\ \le\ (1-p)^{r-1};
--   $$
--   that is, $A_{s_t,t}$ is dominated by $1+\mathrm{Geom}_0(p)$.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: A_{ℓ,t}, the left steps on level ℓ ≥ s_t of the backward walk of charge t → gapA, the levelSteps count of the time-t configuration at level ℓ (nodes y ≤ x_t of time-t height ≥ ℓ with no node of height ≥ ℓ+1 between y and x_t), charges t : Fin σ.length (0-based); reason: the same number as the walk on every level ℓ ≥ s_t, the forced first step on level s_t included and 0 above the maximum height (pp.26–27)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.11, p.27

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_servedHeight
import Definitions.Def_SkipListConc_gapA

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 4.11 (gaps on a search's own level) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip
Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 4.11, p.27). For every charge `t` and every integer `r ≥ 1`,
`Pr[A_{s_t,t} ≥ r] ≤ (1 − p)^{r−1}`; that is, `A_{s_t,t}` is dominated by `1 + Geom₀(p)`.

**Formalization Note** Charges are `t : Fin σ.length` (0-based); the "that is" clause restates the
displayed bound. -/
theorem lemma_4_11 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [LinearOrder α] [MeasurableSpace Ω] (P : Measure Ω)
    (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ)
    (hξ : IsPromotionNoise p K μJ P ξ) (σ : List α) (t : Fin σ.length) (r : ℕ) (hr : 1 ≤ r) :
    P {ω | r ≤ gapA p ξ σ (servedHeight p ξ σ t ω) t ω} ≤
      ENNReal.ofReal ((1 - p) ^ (r - 1)) := by sorry

end SkipListConc
