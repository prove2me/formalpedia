-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_positivePartSmoothing
-- name    : QAlgorithms.Papers.Independent.Support50.P23.positivePartSmoothing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:04:59.347927+00:00
-- url     : https://prove2.me/theorems/5c6ecb30-dfa4-4894-b889-2f621d5cab66
-- title:
--   Positive-part smoothing estimate
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states and $\lambda>0$. Compute $\Delta=(\rho_{AB}-\lambda I_A\otimes\sigma_B)_+$ by positive-part functional calculus and put $\varepsilon=\sqrt{2\operatorname{tr}\Delta}$. Then
--   $$
--   H_{\min}^{\varepsilon}(A|B)_{\rho|\sigma}\ge-\log_2\lambda.
--   $$
--   The radius can be zero or at least one; the closed ball and extended entropy cover these cases. This estimates smooth min entropy from the positive tail of an operator difference.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 8, Lemma 15: positive-part smoothing estimate, (C1)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Lemma 15, PDF p.8, (C1). Radius sqrt(2 tr positivePart) is computed, including
zero and radii>=1. Neither a smoothing witness nor its entropy bound is assumed. -/
theorem positivePartSmoothing [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ((-Real.logb 2 lambda : ℝ) : EReal) ≤
      sineSmoothFixedMin rho sigma (thresholdRadius rho sigma lambda) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
