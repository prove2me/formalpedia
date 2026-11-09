-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_6
-- name    : SkipListConc.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:01.911606+00:00
-- url     : https://prove2.me/theorems/77dc97e1-1416-4cab-b6a9-8c90e1bbae6f
-- title:
--   Lemma 4.6 — exponential moment $\mathbb E[e^{\theta_p D_x(L)/f}]\le e^{C_p(1+(L-\log_b f)_+)}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   There are constants $\theta_p,C_p>0$ depending only on $p$ such that for every item $x$, every $f\ge1$ and every integer $L\ge1$,
--   $$
--   \mathbb E\Bigl[\exp\Bigl(\theta_p\,\frac{D_x(L)}{f}\Bigr)\Bigr]\ \le\ \exp\Bigl(C_p\bigl(1+(L-\log_b f)_+\bigr)\Bigr).
--   $$
--
--   The constants do not depend on $K$, the jump law, the item or the probability space.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: expectation E[exp(·)] → lower Lebesgue integral ∫⁻ of ENNReal.ofReal (exp ·); reason: the integrand is nonnegative; a Bochner integral would be 0 on non-integrable functions
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type (universe 0); reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.6, p.24

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_dVert

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 4.6 (exponential moment for one item) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 4.6, p.24). There are `θ_p, C_p > 0` depending only on `p` such that for every `f ≥ 1` and
every `L ≥ 1`, `E[exp(θ_p D_x(L) / f)] ≤ exp(C_p (1 + (L − log_b f)_+))`, `b = 1/p`.

**Formalization Note** The constants are chosen before `K`, the jump law, the item and the
probability space. The expectation is a lower Lebesgue integral. -/
theorem lemma_4_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ θ C : ℝ, 0 < θ ∧ 0 < C ∧
      ∀ (K : ℕ), 1 ≤ K → ∀ {α Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ (x : α) (f L : ℕ), 1 ≤ f → 1 ≤ L →
          ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (dVert p ξ x f L ω : ℝ) / f)) ∂P ≤
            ENNReal.ofReal
              (Real.exp (C * (1 + max ((L : ℝ) - Real.logb (1 / p) (f : ℝ)) 0))) := by sorry

end SkipListConc
