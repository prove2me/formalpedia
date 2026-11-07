-- Prove2me | Theorems.Thm_StatUnlearn_gaussianReal_tof_comm
-- name    : StatUnlearn.gaussianReal_tof_comm
-- status  : Proved
-- author  : @2017Advanced@
-- created : 2026-11-06T20:10:35.352032+00:00
-- url     : https://prove2.me/theorems/e43a8c53-d3a6-4f13-9105-de3f06c21b99
-- title:
--   Lemma A.1, symmetry in one dimension
-- statement:
--   For Gaussians on the real line with a common variance $v$ and any means $\mu,\nu$, $T(N(\mu,v),N(\nu,v))=T(N(\nu,v),N(\mu,v))$. The reflection $x\mapsto\mu+\nu-x$ is a measurable involution exchanging the two distributions, being the composition of $x\mapsto -x$ (which sends $N(\mu,v)$ to $N(-\mu,v)$) with translation by $\mu+\nu$. This is the one-dimensional case of the symmetry item of Lemma A.1.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, Appendix A.2, Lemma A.1 (`lem: GTOF`), symmetry eq. (A.3)

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_su_tof
open MeasureTheory ProbabilityTheory

namespace StatUnlearn

theorem gaussianReal_tof_comm (μ ν : ℝ) (v : NNReal) :
    tof (gaussianReal μ v) (gaussianReal ν v) = tof (gaussianReal ν v) (gaussianReal μ v) := by
  sorry

end StatUnlearn
