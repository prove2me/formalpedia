-- Prove2me | Theorems.Thm_SkipListConc_lemma_3_4
-- name    : SkipListConc.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:11.353972+00:00
-- url     : https://prove2.me/theorems/39efbfb5-0f46-4da2-be27-3d2f5da79cfd
-- title:
--   Lemma 3.4 — one update preserves $\beta$-thickness
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   Let $0<\beta\le1$, let $x$ be an item and $j\ge1$. Suppose $H_x(j)$ has a $\beta$-thick distribution and the increment $\Delta_c$ is $\beta$-thick for every source height $c\ge1$. Then the distribution of $H_x(j+1)$, after one update with the transition probabilities of Equation (1),
--   $$
--   P(c,c)=1-p^c,\qquad P(c,c+r)=p^c\Pr[\Delta_c=r],\quad r\ge1,
--   $$
--   is $\beta$-thick.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - reading: "after one update with the transition probabilities of Equation (1)" → the update from H_x(j) to H_x(j+1), j ≥ 1, of the height process under IsPromotionNoise; reason: Equation (1) is the transition law of that update; the update is independent of H_x(j)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 3.4, p.17

import Mathlib
import Definitions.Def_SkipListConc_IsThick
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_incrementPMF
import Definitions.Def_SkipListConc_heightPMF

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 3.4 (thickness preservation) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Lemma 3.4, p.17).
Let `0 < β ≤ 1`. Suppose `H_x(j)` has a `β`-thick distribution `μ`, and the increment `Δ_c` is
`β`-thick for every source height `c`. Then the distribution `ν` of `H_x(j + 1)` after one update
with the transition probabilities of Equation (1) is `β`-thick.

**Formalization Note** Stated in the model of Definition 1.1 for `j ≥ 1` (an update, not the
insertion); the increment at source height `c` has law `incrementPMF p μJ c`. -/
theorem lemma_3_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (hξ : IsPromotionNoise p K μJ P ξ) (x : α)
    (j : ℕ) (hj : 1 ≤ j) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hμ : IsThick β (heightPMF P p ξ x j))
    (hΔ : ∀ c : ℕ, 1 ≤ c → IsThick β (incrementPMF p μJ c)) :
    IsThick β (heightPMF P p ξ x (j + 1)) := by sorry

end SkipListConc
