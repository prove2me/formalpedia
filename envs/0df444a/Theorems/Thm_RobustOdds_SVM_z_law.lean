-- Prove2me | Theorems.Thm_RobustOdds_SVM_z_law
-- name    : RobustOdds.SVM.z_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:47.597806+00:00
-- url     : https://prove2.me/theorems/9a259d83-7824-4391-90da-76380a3fc3fa
-- title:
--   Appendix D, p. 17 — law of the pooled weak feature
-- statement:
--   Let $d\ge1$ and let $z=d^{-1/2}\sum_{i=2}^{d+1}x_i$ pool the $d$ independent weak features of model (3). Conditional on any real label value $y$, their joint law gives
--
--   $$z\sim\mathcal N(y\eta\sqrt d,1).$$
--
--   This identifies the one-dimensional Gaussian used to analyze the SVM minimizer.
--
--   **Formalization Note** The theorem permits any real $y$ because the conditional Gaussian family is defined for every real parameter; the model uses $y=\pm1$.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 17, App. D, display defining z

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

open MeasureTheory ProbabilityTheory

theorem z_law (d : ℕ) (hd : 1 ≤ d) (η : ℝ) :
    ∀ y : ℝ, (RobustOdds.Tradeoff.weakLaw d η y).map (fun z => (1 / Real.sqrt d) * ∑ i, z i) =
      gaussianReal (y * η * Real.sqrt d) 1 := by sorry

end RobustOdds.SVM
