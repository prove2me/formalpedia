-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_positiveThresholdExists
-- name    : QAlgorithms.Papers.Independent.Support50.P23.positiveThresholdExists
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:05:53.213723+00:00
-- url     : https://prove2.me/theorems/53eb82b5-f006-4ad3-96b8-2dc2883e8737
-- title:
--   A positive threshold realizing any prescribed radius
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states with $\operatorname{supp}\rho_B\subseteq\operatorname{supp}\sigma_B$, and fix $0\le\varepsilon\le1$. There exists a finite real $\lambda>0$ such that
--   $$
--   \sqrt{2\operatorname{tr}(\rho_{AB}-\lambda I_A\otimes\sigma_B)_+}=\varepsilon,
--   \qquad H_{\min}^{\varepsilon}(A|B)_{\rho|\sigma}\ge-\log_2\lambda.
--   $$
--   This includes both endpoints. It provides a threshold at the specified smoothing radius, as required by the proof of Theorem 7.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 9, Remark 16: choosing a finite positive threshold

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

/-- Remark 16, PDF p.9: a finite POSITIVE threshold realizes the specified radius,
including epsilon=0 and epsilon=1, with the Lemma 15 inequality at that radius. -/
theorem positiveThresholdExists [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : supportedBy (traceLeft rho) sigma)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ lambda : ℝ, 0 < lambda ∧ thresholdRadius rho sigma lambda = epsilon ∧
      ((-Real.logb 2 lambda : ℝ) : EReal) ≤ sineSmoothFixedMin rho sigma epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
