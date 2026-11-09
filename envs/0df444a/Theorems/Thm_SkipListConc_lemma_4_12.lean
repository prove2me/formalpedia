-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_12
-- name    : SkipListConc.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:55:36.334012+00:00
-- url     : https://prove2.me/theorems/dffae6d9-74d4-45f2-9ad9-3262b6c7ee86
-- title:
--   Lemma 4.12 — horizontal cost of all searches $\Pr[C_{\mathrm{hor}}>\gamma_pW_{\mathrm{lev}}+B_pFu]\le e^{-u}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   Let $\sigma$ be an operation sequence of length $F$, $L\ge1$ a cutoff, $C_{\mathrm{hor}}=\sum_{\ell=1}^LC_\ell$ and $W_{\mathrm{lev}}=\sum_{\ell=1}^LW_\ell$. Fix $0<\eta<\ln\frac1{1-p}$ and let
--   $$
--   \gamma_p=\frac{M_p(\eta)-1}{\eta},\qquad B_p=\frac{2+2\ln2+\ln M_p(\eta)+\eta}{\eta}.
--   $$
--   Then for every $u\ge1$,
--   $$
--   \Pr\bigl[C_{\mathrm{hor}}>\gamma_pW_{\mathrm{lev}}+B_pFu\bigr]\ \le\ e^{-u}.
--   $$
--
--   This is the horizontal half of Theorem C.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: A_{ℓ,t}, the left steps on level ℓ ≥ s_t of the backward walk of charge t → gapA, the levelSteps count of the time-t configuration at level ℓ (nodes y ≤ x_t of time-t height ≥ ℓ with no node of height ≥ ℓ+1 between y and x_t), charges t : Fin σ.length (0-based); reason: the same number as the walk on every level ℓ ≥ s_t, the forced first step on level s_t included and 0 above the maximum height (pp.26–27)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.12, p.27

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_Mp
import Definitions.Def_SkipListConc_Wlev
import Definitions.Def_SkipListConc_Chor

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 4.12 (horizontal cost of all searches) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 4.12, p.27). Set `C_hor = ∑_{ℓ=1}^{L} C_ℓ` and `W_lev = ∑_{ℓ=1}^{L} W_ℓ`. Fix
`0 < η < ln(1/(1 − p))` and let `γ_p = (M_p(η) − 1)/η`,
`B_p = (2 + 2 ln 2 + ln M_p(η) + η)/η`. Then for every `u ≥ 1`,
`Pr[C_hor > γ_p W_lev + B_p F u] ≤ e^{−u}`.

**Formalization Note** For every sequence `σ` (of length `F`) and every cutoff `L ≥ 1`. -/
theorem lemma_4_12 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [LinearOrder α] [MeasurableSpace Ω] (P : Measure Ω)
    (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ)
    (hξ : IsPromotionNoise p K μJ P ξ) (σ : List α) (L : ℕ) (hL : 1 ≤ L) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < Real.log (1 / (1 - p))) (u : ℝ) (hu : 1 ≤ u) :
    P {ω | (Mp p η - 1) / η * (Wlev p ξ σ L ω : ℝ) +
          (2 + 2 * Real.log 2 + Real.log (Mp p η) + η) / η * (σ.length : ℝ) * u <
        (Chor p ξ σ L ω : ℝ)} ≤ ENNReal.ofReal (Real.exp (-u)) := by sorry

end SkipListConc
