-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_bayesian_limit69
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.bayesian_limit69
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:27:28.751243+00:00
-- url     : https://prove2.me/theorems/0f16008c-6d3a-485b-8f11-ac5c822241db
-- title:
--   Almost-sure normalized log posterior odds
-- statement:
--   Fix a finite quantum experiment $Q$, a setting law $\sigma$, and an iid trial sequence distributed as $Q_\sigma$ on the product sigma algebra. The competing laws are all potential-outcome local models $P_{\sigma;\pi}$. Let $w$ be a continuous prior density on $\Pi$, normalized for its intrinsic affine-dimensional volume, with $w(\pi)>c>0$ uniformly. Fix a prior hypothesis probability $h\in(0,1)$. For a sample $z^n$, define
--
--   $$m_n(z^n)=\int_\Pi w(\pi)\prod_{i=1}^nP_{\sigma;\pi}(z_i)\,d\pi,\qquad O_n(z^n)=\frac{h}{1-h}\frac{\prod_{i=1}^nQ_\sigma(z_i)}{m_n(z^n)}.$$
--
--   The density is integrable, the iid law has mass one, the target $u(\sigma)=\inf_\pi D_2(Q_\sigma\|P_{\sigma;\pi})$ is finite, and almost surely all quantum and Bayesian sample likelihoods are positive and
--
--   $$\frac{1}{n}\log_2 O_n(Z^n)\longrightarrow u(\sigma).$$
--
--   This is the first-order Bayesian evidence rate proved in (69), with a sublinear log-odds remainder. It does not assert the stronger pathwise logarithmic remainder printed in (46).
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 25, Appendix IV-E: almost-sure normalized log posterior odds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

section ProbabilityCoding

/-- PDF pp.25,29–31, (69): almost-sure normalized log posterior odds, with finite target.
The event explicitly retains positive likelihoods at every n, including n=0. -/
theorem bayesian_limit69 {S : BellExperiment} (Q : Table S) (hQ : NonlocalityProof Q)
    (s : Sigma S) (w : (Potential S → ℝ) → ℝ) (hw : AdmissiblePrior w)
    (h : ℝ) (hpos : 0 < h) (hlt : h < 1) :
    Integrable w (simplexVolume S) ∧
    iidLaw Q s.1 Set.univ = 1 ∧ lowerValue Q s.1 < ⊤ ∧
    ∀ᵐ z ∂iidLaw Q s.1,
      (∀ n, 0 < sampleLikelihood (trialJointLaw Q s.1) (initialTrials z n) ∧
        0 < bayesMarginal s.1 w (initialTrials z n)) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (posteriorOdds Q s.1 w h (initialTrials z n)) / n)
        atTop (𝓝 (lowerValue Q s.1).toReal) := by sorry

end ProbabilityCoding

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
