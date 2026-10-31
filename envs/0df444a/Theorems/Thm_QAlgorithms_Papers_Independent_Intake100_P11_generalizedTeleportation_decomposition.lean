-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_generalizedTeleportation_decomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.generalizedTeleportation_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:53:25.186067+00:00
-- url     : https://prove2.me/theorems/3d907133-78ed-4ebc-b8b0-95bf262e6f5a
-- title:
--   Generalized teleportation: ideal transfer matrix, squeezing and rotations
-- statement:
--   Let $\theta_0,\theta_1$ be the two homodyne angles, put $\theta_+=\theta_0+\theta_1$ and $\theta_-=\theta_0-\theta_1$, and assume $\cos\theta_->0$. Let $R(\alpha)$ be the real plane rotation through $\alpha$, $S(r)=\operatorname{diag}(e^r,e^{-r})$, and $r=\operatorname{artanh}(\sin\theta_-)$. The ideal homogeneous transfer is symplectic and satisfies
--
--   $$
--   T(\theta_+,\theta_-)=\frac1{\cos\theta_-}
--   \begin{pmatrix}\cos\theta_+&\sin\theta_-+\sin\theta_+\\
--   \sin\theta_--\sin\theta_+&\cos\theta_+\end{pmatrix}
--   =R(-\theta_+/2+\pi/4)S(r)R(-\theta_+/2-\pi/4).
--   $$
--
--   Here $\tanh r=\sin\theta_-$. Equivalently, its entries are $\cos\theta_+\cosh r$ on the diagonal and $\pm\sin\theta_+\cosh r+\sinh r$ off the diagonal. In particular $T(\theta,0)=R(-\theta)$, and $T(0,\theta)$ is the displayed 45-degree squeezing when $\cos\theta>0$.
--
--   The transfer also follows directly from the ideal Bell linear relations: for input coordinates $u$, port-output coordinates $v$, and readings $s$, all in $\mathbb R^2$, put $H=\begin{pmatrix}-\cos\theta_0&\sin\theta_0\\\sin\theta_1&\cos\theta_1\end{pmatrix}$ and $L=\begin{pmatrix}\cos\theta_0&\sin\theta_0\\\sin\theta_1&-\cos\theta_1\end{pmatrix}$. If $Hv+Lu=\sqrt2s$, then $v-H^{-1}\sqrt2s=T(\theta_+,\theta_-)u$.
--
--   On the nonsingular domain, simultaneously increasing $\theta_+$ and $\theta_-$ by $\pi$ leaves $T$ unchanged. If $\cos(\theta_0-\theta_1)=0$, the map $v\mapsto Hv$ is not injective, so the two readings cannot invertibly determine both output coordinates. These are ideal Heisenberg coefficient statements, not a claim of exact finite-squeezing teleportation.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 6, §IV, Eqs.(7)–(11); §V, Eq.(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF pp.6--7, Eqs.(7)--(11),(13): corrected ideal linear transfer, rotation
and squeezing decomposition, and singular-angle obstruction. Bell elimination
is a linear Heisenberg identity, not an assumed operational output channel.
Eq.(8)'s printed denominator is corrected as documented above. -/
theorem generalizedTeleportation_decomposition :
    (∀ theta0 theta1 : ℝ, 0 < Real.cos (theta0 - theta1) →
      let thetaPlus := theta0 + theta1
      let thetaMinus := theta0 - theta1
      let r := Real.artanh (Real.sin thetaMinus)
      IsOneModeSymplectic (teleportationMatrix thetaPlus thetaMinus) ∧
      Real.tanh r = Real.sin thetaMinus ∧
      teleportationMatrix thetaPlus thetaMinus = teleportationHyperbolic thetaPlus r ∧
      teleportationMatrix thetaPlus thetaMinus =
        quadratureRotationMatrix (-thetaPlus / 2 + Real.pi / 4) * quadratureSqueezeMatrix r *
          quadratureRotationMatrix (-thetaPlus / 2 - Real.pi / 4) ∧
      ∀ (input output readings : Fin 2 → ℝ),
        (bellOutputMatrix theta0 theta1).mulVec output +
          (bellInputMatrix theta0 theta1).mulVec input = Real.sqrt 2 • readings →
        output - ((bellOutputMatrix theta0 theta1)⁻¹).mulVec (Real.sqrt 2 • readings) =
          (teleportationMatrix thetaPlus thetaMinus).mulVec input) ∧
    (∀ theta : ℝ, teleportationMatrix theta 0 = quadratureRotationMatrix (-theta)) ∧
    (∀ theta : ℝ, 0 < Real.cos theta →
      teleportationMatrix 0 theta =
        quadratureRotationMatrix (Real.pi / 4) * quadratureSqueezeMatrix (Real.artanh (Real.sin theta)) *
          quadratureRotationMatrix (-Real.pi / 4)) ∧
    (∀ thetaPlus thetaMinus : ℝ, Real.cos thetaMinus ≠ 0 →
      teleportationMatrix (thetaPlus + Real.pi) (thetaMinus + Real.pi) =
        teleportationMatrix thetaPlus thetaMinus) ∧
    (∀ theta0 theta1 : ℝ, Real.cos (theta0 - theta1) = 0 →
      ¬ Function.Injective (fun output : Fin 2 → ℝ =>
        (bellOutputMatrix theta0 theta1).mulVec output)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
