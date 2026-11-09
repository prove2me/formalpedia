-- Prove2me | Theorems.Thm_SkipListConc_lemma_2_6
-- name    : SkipListConc.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:53.417259+00:00
-- url     : https://prove2.me/theorems/f955c5da-99d7-42f0-acf6-9c09c2ec2c5a
-- title:
--   Lemma 2.6 — Morris hitting times $\tau_\ell=1+\sum_{r<\ell}G_r$, $G_r\sim\mathrm{Geom}(p^r)$ independent
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   For an item $x$, let $\tau_\ell=\min\{j\ge1: M_x(j)\ge\ell\}$, so $\tau_1=1$. There are independent random variables $G_r$, $r\ge1$, with $G_r\sim\mathrm{Geom}(p^r)$, i.e.
--   $$
--   \Pr[G_r=m]=(1-p^r)^{m-1}p^r,\qquad m\ge1,
--   $$
--   such that
--   $$
--   \tau_\ell=1+\sum_{r=1}^{\ell-1}G_r\qquad\text{for every }\ell\ge2 .
--   $$
--
--   $G_r$ is the time the chain spends at level $r$; this representation makes the lower tail of the height a Chernoff bound for a sum of independent geometrics.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: τ_ℓ and G_r integer valued → τ_ℓ and G_r valued in ℕ∞ (⊤ on the null event that the chain stalls); reason: so that the identity holds on every outcome; the laws give the null event probability 0
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 2.6, p.15

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_Distributions
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_hitTime

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 2.6 (Morris hitting times) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Lemma 2.6, p.15).
With `τ_ℓ = min {j ≥ 1 : M_x(j) ≥ ℓ}`, there are independent `G_r ∼ Geom(p^r)`, `r ≥ 1`
(`Pr[G_r = m] = (1 − p^r)^{m−1} p^r`, `m ≥ 1`), such that `τ_ℓ = 1 + ∑_{r=1}^{ℓ−1} G_r` for every
`ℓ ≥ 2`.

**Formalization Note** `τ_ℓ` and `G_r` take values in `ℕ∞` (value `⊤` on the null event that the
chain stalls), so the identity holds on every outcome. The positive geometric law is the
published `SennottDP.ResidualLife.geomTrials`. -/
theorem lemma_2_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (hξ : IsPromotionNoise p K μJ P ξ) (x : α) :
    ∃ G : ℕ → Ω → ℕ∞,
      (∀ r : ℕ, 1 ≤ r → Measurable (G r) ∧
        ∀ m : ℕ, 1 ≤ m → P {ω | G r ω = m} = SennottDP.ResidualLife.geomTrials (p ^ r) m) ∧
      iIndepFun (fun r : {r : ℕ // 1 ≤ r} => G r) P ∧
      ∀ ω : Ω, ∀ ℓ : ℕ, 2 ≤ ℓ →
        hitTime p ξ x ℓ ω = 1 + ∑ r ∈ Finset.Icc 1 (ℓ - 1), G r ω := by sorry

end SkipListConc
