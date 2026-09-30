-- Prove2me | Theorems.Thm_UnderstandingML_soft_svm_slack_equivalence
-- name    : UnderstandingML.soft_svm_slack_equivalence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:39:08.584029+00:00
-- url     : https://prove2.me/theorems/2a825b6e-beb2-42b1-84c2-8425169882eb
-- title:
--   Claim 15.5: the Soft-SVM problem (15.4) with slacks is equivalent to regularized hinge-loss minimization (15.5): the optimal slacks are the hinge losses
-- statement:
--   **Claim 15.5.** Equation (15.4) and Equation (15.5) are equivalent: for fixed $(w, b)$ the best feasible assignment of the slack variables is $\xi_i = \ell_{hinge}((w,b), (x_i, y_i))$.
--
--   Formally: every feasible slack vector has $\frac1m\sum_i \xi_i \ge L^{hinge}_S((w,b))$, and the hinge losses form a feasible slack vector; hence the two problems have the same value and the same minimizers $(w, b)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.2 p. 207, Claim 15.5 with its proof

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Claim 15.5** (p. 207). Equation (15.4) and Equation (15.5) are equivalent: for fixed
`(w, b)`, the best feasible slack is `ξᵢ = ℓ_hinge((w, b), (xᵢ, yᵢ))`. Stated as: every feasible
slack vector has `(1/m) ∑ ξᵢ ≥ L^hinge_S((w, b))`, and the hinge losses form a feasible slack
vector (whose average is `L^hinge_S((w, b))`), so the two minimization problems have the same
value and the same minimizers `(w, b)`. -/
theorem soft_svm_slack_equivalence {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) :
    (∀ (w : Vec d) (b : ℝ) (ξ : Fin m → ℝ), SoftSVMFeasible x y w b ξ →
      (∑ i, hingeLossAffine w b (x i, y i)) / m ≤ (∑ i, ξ i) / m) ∧
    ∀ (w : Vec d) (b : ℝ),
      SoftSVMFeasible x y w b (fun i ↦ hingeLossAffine w b (x i, y i)) := by sorry

end UnderstandingML
