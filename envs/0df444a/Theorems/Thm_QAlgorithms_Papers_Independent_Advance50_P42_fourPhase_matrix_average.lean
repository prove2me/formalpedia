-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P42_fourPhase_matrix_average
-- name    : QAlgorithms.Papers.Independent.Advance50.P42.fourPhase_matrix_average
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:06:09.481757+00:00
-- url     : https://prove2.me/theorems/1e6c17bb-dd56-4c3c-9fe4-332a13189dc8
-- title:
--   Four opposite phase rotations: exact symmetric matrix average and polar form
-- statement:
--   Let $\sigma=(\sigma_{ij})_{i,j=1}^4$ be an arbitrary symmetric real matrix and let
--   $$
--   X(\phi)=\begin{pmatrix}
--   \cos\phi&\sin\phi&0&0\\-\sin\phi&\cos\phi&0&0\\
--   0&0&\cos\phi&-\sin\phi\\0&0&\sin\phi&\cos\phi
--   \end{pmatrix}.
--   $$
--   Its average over the four phases is exactly
--   $$
--   \frac14\sum_{k=0}^{3}X(\pi k/2)\sigma X(\pi k/2)^{T}
--   =\frac12\begin{pmatrix}
--   \sigma_{11}+\sigma_{22}&0&\sigma_{13}-\sigma_{24}&\sigma_{14}+\sigma_{23}\\
--   0&\sigma_{11}+\sigma_{22}&\sigma_{14}+\sigma_{23}&-(\sigma_{13}-\sigma_{24})\\
--   \sigma_{13}-\sigma_{24}&\sigma_{14}+\sigma_{23}&\sigma_{33}+\sigma_{44}&0\\
--   \sigma_{14}+\sigma_{23}&-(\sigma_{13}-\sigma_{24})&0&\sigma_{33}+\sigma_{44}
--   \end{pmatrix}.
--   $$
--   Equivalently this matrix is $\begin{pmatrix}a&0&c_2&c_1\\0&a&c_1&-c_2\\c_2&c_1&b&0\\c_1&-c_2&0&b\end{pmatrix}$, where $a=(\sigma_{11}+\sigma_{22})/2$, $b=(\sigma_{33}+\sigma_{44})/2$, $c_1=(\sigma_{14}+\sigma_{23})/2$, and $c_2=(\sigma_{13}-\sigma_{24})/2$. With $z=\sqrt{c_1^2+c_2^2}$ there exists $\theta\in\mathbb R$ such that $c_1=z\sin\theta$ and $c_2=z\cos\theta$, giving the entire polar matrix in (157), including $z=0$.
--
--   This identity describes the finite matrix average in Appendix B. For an arbitrary real symmetric matrix no uncertainty constraint or bounds $a,b\ge1$ are asserted. Applying it to the centered covariance of a mixed quantum state requires a separate means argument.
--
--   **Formalization Note** Coordinates are zero-based in Lean. The printed formula $\theta=\arctan(c_1/c_2)$ is replaced by existence of a polar angle, avoiding division by zero and the wrong quadrant. This is the pinned correction for the algebraic node; independent moderation is pending.
-- source:
--   Asymptotic security of discrete-modulation protocols for continuous-variable quantum key distribution, arXiv:1901.10099v4, PDF p. 21, Appendix B, (153)–(157)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P42

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Advance50.P42

/-- Appendix B, (153)--(157), PDF pp.20--21: the full four-phase real-matrix
identity, parameter identifications, and polar representation.
Source correction: the printed arctan(c1/c2) is replaced by existence of an angle,
which is the polar-representation claim used by (157), valid also when c2=0
or both mixed entries vanish. The arbitrary symmetric-matrix scope does not imply
these matrices are quantum covariances, nor the physical bounds a,b >= 1. -/
theorem fourPhase_matrix_average
    (sigma : Matrix (Fin 4) (Fin 4) ℝ) (hsigma : sigma.IsSymm) :
    let a := (sigma 0 0 + sigma 1 1) / 2
    let b := (sigma 2 2 + sigma 3 3) / 2
    let c1 := (sigma 0 3 + sigma 1 2) / 2
    let c2 := (sigma 0 2 - sigma 1 3) / 2
    let z := Real.sqrt (c1 ^ 2 + c2 ^ 2)
    fourPhaseAverage sigma = (1 / 2 : ℝ) •
      !![sigma 0 0 + sigma 1 1, 0, sigma 0 2 - sigma 1 3, sigma 0 3 + sigma 1 2;
         0, sigma 0 0 + sigma 1 1, sigma 0 3 + sigma 1 2, -(sigma 0 2 - sigma 1 3);
         sigma 0 2 - sigma 1 3, sigma 0 3 + sigma 1 2, sigma 2 2 + sigma 3 3, 0;
         sigma 0 3 + sigma 1 2, -(sigma 0 2 - sigma 1 3), 0, sigma 2 2 + sigma 3 3] ∧
    fourPhaseAverage sigma = phaseSymmetricMatrix a b c1 c2 ∧
    ∃ theta : ℝ, c1 = z * Real.sin theta ∧ c2 = z * Real.cos theta ∧
      fourPhaseAverage sigma =
        phaseSymmetricMatrix a b (z * Real.sin theta) (z * Real.cos theta) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P42

end
