-- Prove2me | Theorems.Thm_SkipListConc_lemma_3_2
-- name    : SkipListConc.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:02.549656+00:00
-- url     : https://prove2.me/theorems/53ad64ab-9d0d-44f7-aa05-a2bfa34266dc
-- title:
--   Lemma 3.2 — the increment distribution $J+G$ is $p$-thick
-- statement:
--   Fix $0<p<1$.
--
--   1. Let $J$ be any random variable on the positive integers and let $G\sim\mathrm{Geom}_0(1-p)$ be independent of it. Then the distribution of $J+G$ is $p$-thick.
--   2. In particular, for every jump law and every source height $c\ge1$, the increment $\Delta_c=J_c+G$ of Definition 1.1 is $p$-thick,
--   3. and so is the distribution of the initial height $H_x(1)=J_0+G_0$.
--
--   The terminal geometric component creates thickness whatever the jump law.
--
--   Differences from the source:
--   - encoding: distributions on the positive integers → sequences of point masses r ↦ Pr[· = r] (IsThick); reason: a distribution on a countable set is its point masses
--   - encoding: J a random variable on the positive integers → ℕ-valued measurable J with J ≥ 1 on every outcome; reason: values in the positive integers
--   - encoding: the increment Δ_c and H_x(1) of Definition 1.1 → incrementPMF p μJ c for every probability law μJ of jump tables, and the law of height x 1 under IsPromotionNoise; reason: the model of Definition 1.1 (see IsPromotionNoise)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 3.2, p.16

import Mathlib
import Definitions.Def_SkipListConc_geom0
import Definitions.Def_SkipListConc_IsThick
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_incrementPMF
import Definitions.Def_SkipListConc_heightPMF

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 3.2 (the increment distribution is `p`-thick) (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), Lemma 3.2, p.16). Let `J` be any random variable on the positive integers and
`G ∼ Geom₀(1 − p)` independent of it. Then the distribution of `J + G` is `p`-thick. In
particular, for every source height `c` the increment `Δ_c = J_c + G` of Definition 1.1 is
`p`-thick, and so is the distribution of the initial height `H_x(1) = J₀ + G₀`.

**Formalization Note** Three clauses: the general statement on any probability space; the
increment law `incrementPMF` at every `c ≥ 1` for every jump law; and the law of `H_x(1)` under
the promotion noise. -/
theorem lemma_3_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (J G : Ω' → ℕ), Measurable J → Measurable G → (∀ ω, 1 ≤ J ω) →
        P'.map G = geom0 p → IndepFun J G P' →
        IsThick p (fun r => (P' {ω | J ω + G ω = r}).toReal)) ∧
      (∀ (K : ℕ), 1 ≤ K → ∀ (μJ : Measure (ℕ → Fin K)), IsProbabilityMeasure μJ →
        ∀ c : ℕ, 1 ≤ c → IsThick p (incrementPMF p μJ c)) ∧
      (∀ (K : ℕ), 1 ≤ K → ∀ {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
        IsPromotionNoise p K μJ P ξ → ∀ x : α, IsThick p (heightPMF P p ξ x 1)) := by sorry

end SkipListConc
