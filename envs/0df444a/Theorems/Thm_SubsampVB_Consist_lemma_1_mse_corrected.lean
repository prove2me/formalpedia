-- Prove2me | Theorems.Thm_SubsampVB_Consist_lemma_1_mse_corrected
-- name    : SubsampVB.Consist.lemma_1_mse_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:17.440979+00:00
-- url     : https://prove2.me/theorems/4311bf27-3956-439a-a90c-3bb2be8855f5
-- title:
--   Lemma 1, (18), corrected — conditional mean squared error
-- statement:
--   Under Assumptions 1–7, let $B\to\infty$, $\theta n\to\infty$, $R\ge2$, and let the true-model simulation variance $\tau^2$ be positive. Write $\sigma_i^2$ for the $i$th influence-function variance. The conditional mean squared error of Algorithm 2 has the corrected leading form
--
--   $$\frac{\mathbb E_*[(\widehat\sigma_{SVB}^2-\sigma_{SVB}^2)^2]}{\frac2B\left[\left(\sum_i\frac{\sigma_i^2}{n_i}+\frac{\tau^2\theta}{R}\right)^2+\frac{\tau^4\theta^2}{R^2(R-1)}\right]}\xrightarrow{\mathrm p}1.$$
--
--   The displayed equation (18) in the preprint omits the last term. For bounded $R$ it is false: with a negligible input contribution, fair $\pm1$ simulation noise, $R=2$, and $\theta=1$, the leading $B$-scaled MSE is $1$, whereas the printed expression gives $1/2$. Positive influence variances still permit a negligible contribution as the input sample sizes diverge. The added term gives the correct leading constant. Positivity of $\tau^2$ rules out another degeneration of the claimed relative expansion.
--
--   **Formalization Note** The corrected target is intentionally distinct from the printed equation; the discrepancy is recorded in the moderation notes.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, p. 25, Lemma 1 and (18), corrected; proof p. ec14 (PDF 64)

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

namespace SubsampVB.Consist

open MeasureTheory Filter Finset

universe u v

/-- Lemma 1, equation (18), p. 25, corrected for bounded R. -/
theorem lemma_1_mse_corrected
    {m : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ) (B R : ℕ → ℕ)
    (hS : ∀ i, MeasurableSet (S i) ∧ F i (S i)ᶜ = 0)
    (hData : IIDData P F X) (hOracle : SimOracle ψ simLaw)
    (hTauFinite : Integrable (fun y => (y - ψ F) ^ 2) (simLaw F))
    (hTauPositive : 0 < tau2 ψ simLaw F)
    (hA1 : A1 n) (hA2 : A2 F S ψ g) (hA3 : A3 P F ψ g X n)
    (hA4 : A4 P F ψ g X n θ) (hA5 : A5 P F ψ simLaw X n)
    (hA6 : A6 P ψ simLaw X n θ) (hA7 : A7 P ψ simLaw X n θ)
    (hParams : ∀ k, 2 ≤ B k ∧ 2 ≤ R k ∧ 0 < θ k ∧ θ k ≤ 1)
    (hB : Tendsto (fun k => (B k : ℝ)) atTop atTop)
    (hθn : Tendsto (fun k => θ k * nbar (n k)) atTop atTop) :
    TendstoInMeasure P (fun k ω =>
      outMSE (B := B k) (R := R k) ψ simLaw (n := n k)
        (s := subsampleSize (θ k) (n k)) (θ k) (dataSample X (n k) ω) /
      ((2 / (B k : ℝ)) *
        (((∑ i : Fin m, sigma2 F g i / (n k i : ℝ)) +
            tau2 ψ simLaw F * θ k / (R k : ℝ)) ^ 2 +
          ((tau2 ψ simLaw F) ^ 2 * (θ k) ^ 2 /
            ((R k : ℝ) ^ 2 * ((R k : ℝ) - 1))))))
      atTop (fun _ => 1) := by sorry

end SubsampVB.Consist
