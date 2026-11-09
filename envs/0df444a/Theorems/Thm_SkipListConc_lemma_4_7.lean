-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_7
-- name    : SkipListConc.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:51.175799+00:00
-- url     : https://prove2.me/theorems/ec4f9d09-6184-4df1-bc83-fa201512c08f
-- title:
--   Lemma 4.7 — tail of the vertical cost $\Pr[D(L)>C'_p\Phi(L)+(F/c_p)u]\le e^{-u}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   Let $D(L)=\sum_xD_x(L)$ and $\Phi(L)=\sum_xf_x\bigl(1+(L-\log_bf_x)_+\bigr)$, the sums over the distinct items of an operation sequence $\sigma$ of length $F$. There are constants $c_p,C'_p>0$ depending only on $p$ such that for every $\sigma$, every cutoff $L\ge1$ and every $u\ge0$,
--   $$
--   \Pr\Bigl[D(L)>C'_p\,\Phi(L)+\frac{F}{c_p}\,u\Bigr]\ \le\ e^{-u}.
--   $$
--
--   This is the vertical half of Theorem C: the entropy enters through $\Phi(L)$.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type (universe 0); reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.7, p.25

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_vertCost
import Definitions.Def_SkipListConc_phiBench

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 4.7 (tail bound for the vertical cost) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 4.7, p.25). Let `D(L) = ∑_x D_x(L)` and `Φ(L) = ∑_x f_x (1 + (L − log_b f_x)_+)`. There
are `c_p, C'_p > 0` depending only on `p` such that for every `u ≥ 0`,
`Pr[D(L) > C'_p Φ(L) + (F / c_p) u] ≤ e^{−u}`.

**Formalization Note** The constants are chosen before `K`, the jump law, the sequence `σ`
(of length `F`), the cutoff `L ≥ 1` and the probability space. -/
theorem lemma_4_7 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
      ∀ (K : ℕ), 1 ≤ K → ∀ {α : Type} [DecidableEq α] (σ : List α) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ L : ℕ, 1 ≤ L → ∀ u : ℝ, 0 ≤ u →
          P {ω | C' * phiBench p σ L + (σ.length : ℝ) / c * u < (vertCost p ξ σ L ω : ℝ)} ≤
            ENNReal.ofReal (Real.exp (-u)) := by sorry

end SkipListConc
