-- Prove2me | Theorems.Thm_SkipListConc_lemma_2_7
-- name    : SkipListConc.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:50:12.192287+00:00
-- url     : https://prove2.me/theorems/18bc9f21-9e4c-4ebd-8556-c2e077d17e21
-- title:
--   Lemma 2.7 — MGF of a geometric waiting time: $\mathbb E[e^{\lambda G}]\le e^{2\lambda/q}$ for $0\le\lambda\le q/2$
-- statement:
--   Let $G$ be a positive geometric random variable with parameter $q\in(0,1]$, that is
--   $$
--   \Pr[G=m]=(1-q)^{m-1}q,\qquad m\ge1 .
--   $$
--   If $0\le\lambda\le q/2$, then
--   $$
--   \mathbb E\bigl[e^{\lambda G}\bigr]\ \le\ \exp(2\lambda/q).
--   $$
--
--   It is the exponential-moment bound applied to each Morris waiting time $G_r\sim\mathrm{Geom}(p^r)$.
--
--   Differences from the source:
--   - encoding: expectation E[exp(·)] → lower Lebesgue integral ∫⁻ of ENNReal.ofReal (exp ·); reason: the integrand is nonnegative; a Bochner integral would be 0 on non-integrable functions
--   - encoding: "positive geometric with parameter q" → 0 < q ≤ 1, law SennottDP.ResidualLife.geomTrials q on m ≥ 1; reason: the range of q for which the formula is a probability law; the published definition is exactly (1 − q)^{m−1} q
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 2.7, p.15 (proof in Appendix II.1, p.53)

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_Distributions

open MeasureTheory

namespace SkipListConc

/-- Lemma 2.7 (MGF of a geometric waiting time) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 2.7, p.15; proof in Appendix II.1, p.53). Let `G` be positive geometric with parameter `q`,
`Pr[G = m] = (1 − q)^{m−1} q` for `m ≥ 1`. If `0 ≤ λ ≤ q/2` then `E[e^{λG}] ≤ exp(2λ/q)`.

**Formalization Note** The parameter `q ∈ (0, 1]`. The expectation of the nonnegative variable
`e^{λG}` is a lower Lebesgue integral. The law is the published
`SennottDP.ResidualLife.geomTrials`. -/
theorem lemma_2_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (G : Ω → ℕ) (hG : Measurable G)
    (hlaw : ∀ m : ℕ, 1 ≤ m → P {ω | G ω = m} = SennottDP.ResidualLife.geomTrials q m)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ q / 2) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (G ω : ℝ))) ∂P ≤
      ENNReal.ofReal (Real.exp (2 * lam / q)) := by sorry

end SkipListConc
