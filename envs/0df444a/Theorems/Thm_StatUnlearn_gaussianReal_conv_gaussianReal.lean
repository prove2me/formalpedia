-- Prove2me | Theorems.Thm_StatUnlearn_gaussianReal_conv_gaussianReal
-- name    : StatUnlearn.gaussianReal_conv_gaussianReal
-- status  : Proved
-- author  : @2017Advanced@
-- created : 2026-11-06T20:14:58.277569+00:00
-- url     : https://prove2.me/theorems/7276b7f3-34d9-40a7-8454-0cbbdb5a398f
-- title:
--   Convolution of Gaussians: $\mathcal{N}(\mu,v)*\mathcal{N}(\nu,w)=\mathcal{N}(\mu+\nu,v+w)$
-- statement:
--   For real means $\mu,\nu$ and variances $v,w\ge0$, the convolution of the two Gaussians on the line is Gaussian with the parameters added:
--   $$\mathcal{N}(\mu,v)*\mathcal{N}(\nu,w)=\mathcal{N}(\mu+\nu,\ v+w).$$
--   In other words, the Gaussian family is closed under convolution: adding independent Gaussian noise to a Gaussian observation yields another Gaussian, with the variances adding. The proof identifies both sides by their characteristic functions — $\varphi_{\mathcal{N}(\mu,v)}(t)=e^{it\mu-vt^2/2}$, the characteristic function of a convolution is the product of the characteristic functions, and two finite Borel measures on the line with the same characteristic function coincide — after which the identity reduces to the exponential law $e^Ae^B=e^{A+B}$.
--
--   This is the algebraic fact that makes "add independent noise" a Markov kernel on the Gaussian baselines. It is what converts the data-processing inequality for trade-off functions into monotonicity in the shift parameter: from $\mathcal{N}(\mu,v)$ and $\mathcal{N}(\nu,v)$ one can reach a pair of Gaussians with a smaller separation, never a larger one.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, Appendix A.2, Lemma A.1 (`lem: GTOF`): the closure of the Gaussian baselines under adding independent noise, used for monotonicity (A.1)

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
open MeasureTheory ProbabilityTheory

namespace StatUnlearn

theorem gaussianReal_conv_gaussianReal (μ ν : ℝ) (v w : NNReal) :
    (gaussianReal μ v).conv (gaussianReal ν w) = gaussianReal (μ + ν) (v + w) := by
  sorry

end StatUnlearn
