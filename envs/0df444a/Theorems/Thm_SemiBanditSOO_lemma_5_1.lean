-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_1
-- name    : SemiBanditSOO.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:41.330907+00:00
-- url     : https://prove2.me/theorems/2b870a51-747a-4de9-a520-1ead82c91296
-- title:
--   Lemma 5.1 — empirical Bernstein bound for $|P(I)-\widehat P_m(I)|$, uniformly over intervals $I\in\mathcal I_1$
-- statement:
--   Let $m\ge16$ and $\eta\in(0,1)$, and let $\widehat P_m$ be the empirical distribution of i.i.d. samples $Z_1,\dots,Z_m$ from a distribution $P$ on $[0,1]$. With probability at least $1-\eta$, simultaneously for all intervals $I\in\mathcal I_1$,
--   $$|P(I)-\widehat P_m(I)|\le\sqrt{\frac{18\,\widehat P_m(I)(1-\widehat P_m(I))\,\beta}{m-1}}+\frac{15\beta}{m-1},\qquad \beta=\log\frac{20(2m+1)^2}{\eta}. \qquad (5.1)$$
--
--   This interval form of the empirical Bernstein inequality of Maurer and Pontil gives the coverage of the confidence sets (Lemma 5.2).
--
--   **Formalization Note.** $P$ is a probability measure on $\mathbb R$ with full mass on $[0,1]$, and the samples are the coordinates of $Z\sim P^{\otimes m}$.
--
--   Differences from the source:
--   - encoding: a distribution P on [0, 1] → a probability measure on ℝ with P([0, 1]ᶜ) = 0; reason: the same distributions
--   - encoding: with probability at least 1 − η → the (outer) measure of the failure event is at most η; reason: the same statement; no measurability of the failure event needs to be proved
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.1, (5.1), p.20; proved in Appendix C, p.40

import Mathlib
import Definitions.Def_SemiBanditSOO_LevelSet

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.1 (empirical Bernstein bound, uniformly over intervals).** Harada, Kawase, Sumita,
*Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*,
arXiv:2611.02739v1, Lemma 5.1, (5.1), p.20.

Let `m ≥ 16` and `η ∈ (0, 1)`, and let `P̂_m` be the empirical distribution of i.i.d. samples
`Z_1, …, Z_m` from a distribution `P` on `[0, 1]`. With probability at least `1 − η`, simultaneously
for all `I ∈ ℐ₁`,
`|P(I) − P̂_m(I)| ≤ √(18 P̂_m(I)(1 − P̂_m(I)) β / (m − 1)) + 15 β / (m − 1)`,
where `β = log(20(2m + 1)²/η)`.

**Formalization Note.** `P` is a probability measure on `ℝ` giving full mass to `[0, 1]`; the
samples are the coordinates of `Z ∼ P^{⊗m}`; `P̂_m(I) = (1/m) Σ_j 1{Z_j ∈ I}`. "With probability at
least `1 − η`" is stated as: the (outer) measure of the event that the bound fails for some
`I ∈ ℐ₁` is at most `η`. -/
theorem lemma_5_1 (m : ℕ) (hm : 16 ≤ m) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P (Set.Icc 0 1)ᶜ = 0) :
    (Measure.pi fun _ : Fin m => P)
      {Z : Fin m → ℝ | ∃ I ∈ IntervalUnions 1,
        Real.sqrt (18 * ((∑ j, I.indicator (fun _ => (1 : ℝ)) (Z j)) / m) *
            (1 - (∑ j, I.indicator (fun _ => (1 : ℝ)) (Z j)) / m) *
            Real.log (20 * (2 * (m : ℝ) + 1) ^ 2 / η) / ((m : ℝ) - 1)) +
          15 * Real.log (20 * (2 * (m : ℝ) + 1) ^ 2 / η) / ((m : ℝ) - 1) <
        |P.real I - (∑ j, I.indicator (fun _ => (1 : ℝ)) (Z j)) / m|}
      ≤ ENNReal.ofReal η := by sorry

end SemiBanditSOO
