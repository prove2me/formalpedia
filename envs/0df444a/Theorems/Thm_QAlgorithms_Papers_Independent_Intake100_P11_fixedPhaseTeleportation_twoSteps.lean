-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_fixedPhaseTeleportation_twoSteps
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.fixedPhaseTeleportation_twoSteps
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:54:23.545987+00:00
-- url     : https://prove2.me/theorems/d455b1fc-9a51-4b00-8e59-66452f2e0a1d
-- title:
--   Fixed coupling requires two further elementary gates for universality
-- statement:
--   Let $M(t)=\begin{pmatrix}-t&-1\\1&0\end{pmatrix}$, let $T$ be the ideal fixed-coupling teleportation matrix, and write its equivalent real parametrization as
--
--   $$
--   T'(\theta,r)=\begin{pmatrix}\cos\theta\cosh r&\sin\theta\cosh r+\sinh r\\-\sin\theta\cosh r+\sinh r&\cos\theta\cosh r\end{pmatrix},\qquad \theta,r\in\mathbb R.
--   $$
--
--   Its first-row range consists exactly of the pairs $(a,b)$ satisfying $b\ne0$ or $a=1$ or $a=-1$. Nevertheless, for every $S\in\operatorname{Sp}(2,\mathbb R)$ there are real $\theta_+,\theta_-,k_3,k_4$ such that
--
--   $$
--   \cos\theta_->0,\qquad M(k_4)M(k_3)T(\theta_+,\theta_-)=S.
--   $$
--
--   The source's two port modes followed by two extra elementary modules use four ancillas. Both smaller families, $T$ alone and $M(k_3)T$, miss some symplectic targets. This gives necessity and sufficiency in the fixed beam-splitter and local-homodyne architecture of Fig.4, without asserting minimality over arbitrary graphs.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 7, §V, Eq.(13) and unnumbered proof

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF p.7, Eq.(13) and Q.E.D. proof: fixed-coupling prefix plus two elementary
steps is universal, while zero or one extra step is not. Includes its exact
first-row obstruction. The equivalent parameter r ranges over all reals. -/
theorem fixedPhaseTeleportation_twoSteps :
    (∀ a b : ℝ,
      (∃ theta r : ℝ, teleportationHyperbolic theta r 0 0 = a ∧
        teleportationHyperbolic theta r 0 1 = b) ↔
        (b ≠ 0 ∨ a = 1 ∨ a = -1)) ∧
    (∀ A : Mat2, IsOneModeSymplectic A →
      ∃ thetaPlus thetaMinus kappa3 kappa4 : ℝ,
        0 < Real.cos thetaMinus ∧
        teleportationAncillas [kappa3, kappa4] = 4 ∧
        elementary kappa4 * elementary kappa3 *
          teleportationMatrix thetaPlus thetaMinus = A) ∧
    (∃ A : Mat2, IsOneModeSymplectic A ∧
      ∀ thetaPlus thetaMinus : ℝ, 0 < Real.cos thetaMinus →
        teleportationMatrix thetaPlus thetaMinus ≠ A) ∧
    (∃ A : Mat2, IsOneModeSymplectic A ∧
      ∀ thetaPlus thetaMinus kappa3 : ℝ, 0 < Real.cos thetaMinus →
        elementary kappa3 * teleportationMatrix thetaPlus thetaMinus ≠ A) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
