-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_compression_limit85
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.compression_limit85
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:28:32.840661+00:00
-- url     : https://prove2.me/theorems/017197e7-89f3-44f6-8344-2dc3bd64e62d
-- title:
--   Bayesian Shannon-code evidence rate
-- statement:
--   Fix the quantum experiment, setting law, iid trials, and continuous uniformly positive normalized local-theory prior of the Bayesian limit. Let $m_n$ be the actual Bayesian marginal likelihood. On its positive-probability support, use the Shannon binary code obtained by sorting words by decreasing $m_n$ probability, breaking ties by a fixed finite enumeration, and taking the first $\lceil-\log_2m_n(z^n)\rceil$ binary digits of the cumulative probability. The resulting words form a prefix code and have lengths $L_n$ satisfying
--
--   $$-\log_2m_n(z^n)\le L_n(z^n)<-\log_2m_n(z^n)+1.$$
--
--   The iid law is a probability measure, the prior is integrable, and $u(\sigma)=\inf_\pi D_2(Q_\sigma\|P_{\sigma;\pi})$ is finite. Almost surely every observed word has positive quantum and Bayesian likelihood, and
--
--   $$\frac{L_n(Z^n)-[-\log_2 Q_\sigma(Z^n)]}{n}\longrightarrow u(\sigma).$$
--
--   This gives the information-theoretic evidence rate (53), (85) for an actual support-restricted code; impossible words are excluded from its coding alphabet.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 27, Appendix IV-F: Bayesian/Shannon code evidence rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

section ProbabilityCoding

/-- PDF pp.27,29,31, (53),(85): the explicit support-restricted Bayesian/Shannon code.
Its words have the source's ceiling lengths, and its excess over ideal Q length has the KL rate.
This is normalized convergence, not the invalid pathwise O(log n) claim in (46). -/
theorem compression_limit85 {S : BellExperiment} (Q : Table S) (hQ : NonlocalityProof Q)
    (s : Sigma S) (w : (Potential S → ℝ) → ℝ) (hw : AdmissiblePrior w) :
    Integrable w (simplexVolume S) ∧ iidLaw Q s.1 Set.univ = 1 ∧ lowerValue Q s.1 < ⊤ ∧
    (∀ n, IsPrefixCode (fun z : {z : Fin n → BellTrial S // 0 < bayesMarginal s.1 w z} =>
      shannonWord (fun t : Fin n → BellTrial S => bayesMarginal s.1 w t) z.1)) ∧
    (∀ n (z : Fin n → BellTrial S), 0 < bayesMarginal s.1 w z →
      let L := ((shannonWord (fun t : Fin n → BellTrial S => bayesMarginal s.1 w t) z).length : ℝ);
      -Real.logb 2 (bayesMarginal s.1 w z) ≤ L ∧ L < -Real.logb 2 (bayesMarginal s.1 w z) + 1) ∧
    ∀ᵐ z ∂iidLaw Q s.1,
      (∀ n, 0 < sampleLikelihood (trialJointLaw Q s.1) (initialTrials z n) ∧
        0 < bayesMarginal s.1 w (initialTrials z n)) ∧
      Tendsto (fun n : ℕ =>
        (((shannonWord (fun t : Fin n → BellTrial S => bayesMarginal s.1 w t)
          (initialTrials z n)).length : ℝ) + Real.logb 2 (sampleLikelihood (trialJointLaw Q s.1) (initialTrials z n))) / n)
        atTop (𝓝 (lowerValue Q s.1).toReal) := by sorry

end ProbabilityCoding

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
