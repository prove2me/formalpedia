-- Prove2me | Theorems.Thm_SubsampVB_Consist_lemma_1_unbiased
-- name    : SubsampVB.Consist.lemma_1_unbiased
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:24.241154+00:00
-- url     : https://prove2.me/theorems/9f6caa11-5cea-43f6-96b5-6d28c5bb2b3b
-- title:
--   Lemma 1 — conditional unbiasedness of Algorithm 2
-- statement:
--   Fix observed data from $m\ge1$ input processes with $n_i\ge1$, a subsample ratio $0<\theta\le1$ with $s_i=\lfloor\theta n_i\rfloor\ge1$, and integers $B,R\ge2$. Suppose each simulation replication under the resampled input laws has mean $\psi$ of those laws and a finite second moment. If $\widehat\sigma_{SVB}^2$ is Algorithm 2's ANOVA output and $\sigma_{SVB}^2$ is the ideal resampling variance, then
--
--   $$\mathbb E_*[\widehat\sigma_{SVB}^2]=\sigma_{SVB}^2.$$
--
--   The conditional expectation covers both the with-replacement index maps and the independent simulation replications. This exact identity separates systematic error from Monte Carlo variability.
--
--   **Formalization Note** The simulation responses are distributed according to finite product measures. Positive sample sizes and second-moment integrability make the conditional expectation a genuine expectation.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, p. 25, Lemma 1, first sentence; Algorithm 2 p. 15

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

namespace SubsampVB.Consist

open MeasureTheory Finset

universe u

/-- Lemma 1, first sentence, p. 25: exact conditional unbiasedness. -/
theorem lemma_1_unbiased
    {m B R : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    (n : Fin m → ℕ) (θ : ℝ) (x : Sample Ξ n)
    (hB : 2 ≤ B) (hR : 2 ≤ R) (hθ : 0 < θ ∧ θ ≤ 1)
    (hn : ∀ i, 1 ≤ n i) (hs : ∀ i, 1 ≤ subsampleSize θ n i)
    (hOracle : SimOracle ψ simLaw)
    (hSecond : ∀ I : Resample n (subsampleSize θ n),
      Integrable (fun y => (y - ψ (Fbar univ I x)) ^ 2)
        (simLaw (Fbar univ I x))) :
    (Fintype.card (Fin B → Resample n (subsampleSize θ n)) : ℝ)⁻¹ *
      ∑ I : Fin B → Resample n (subsampleSize θ n),
        ∫ Y, sigmaHatSVB θ Y ∂(outputLaw (R := R) simLaw I x) =
      sigmaSVB ψ θ x := by sorry

end SubsampVB.Consist
