-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P59_principalFormAndStabilizer
-- name    : QAlgorithms.Papers.Independent.Information100.P59.principalFormAndStabilizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:27:20.205272+00:00
-- url     : https://prove2.me/theorems/dacb0118-586a-467a-a7c0-1ae23dbdab33
-- title:
--   Corollary 3.8: Principal jump form and rotational stabilizer
-- statement:
--   Write $D_L(X)=LXL^\dagger-\{L^\dagger L,X\}/2$. For every nonzero $a\in\mathbb C^3$, there exist a phase $\varphi$, real numbers $s>0$ and $0\le t\le s$, and a positively oriented orthonormal frame $(\widehat\alpha,\widehat\beta,\widehat\nu)$ such that $e^{i\varphi}a=s\widehat\alpha+it\widehat\beta$, with $\widehat\nu=\widehat\alpha\times\widehat\beta$. This phase leaves $D_{a\cdot\sigma}$ unchanged. In that frame,
--
--   $$Q=\operatorname{diag}(-2t^2,-2s^2,-2(s^2+t^2)),\qquad b=4st\widehat\nu.$$
--
--   The channel is unital exactly when $t=0$. Its full affine Bloch data have a continuous rotation axis exactly when $t=0$ or $t=s$. For $0<t<s$, the proper rotational stabilizer consists precisely of the identity and the half-turn about $\widehat\nu$.
--
--   At $t=0$ the frame is an orthonormal completion; no division by the vanishing imaginary component is required.
-- source:
--   Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control, arXiv:2610.00046v1, PDF p. 12, Corollary 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF p.12, Corollary 3.8. An orthonormal completion is
existential even when t=0; no normalization of the zero imaginary part is used. -/
theorem principalFormAndStabilizer (a : Cvec) (ha : a ≠ 0) :
    ∃ (phase s t : ℝ) (R : Mat), IsRotation R ∧ 0 < s ∧ 0 ≤ t ∧ t ≤ s ∧
      (∀ j, Complex.exp (Complex.I * (phase : ℂ)) * a j =
        (s * R j 0 : ℝ) + Complex.I * (t * R j 1 : ℝ)) ∧
      (∀ X : Qmat, dissipator (jump (fun j => Complex.exp (Complex.I * (phase : ℂ)) * a j)) X =
        dissipator (jump a) X) ∧
      R.transpose * operatorQ a * R = Matrix.diagonal ![-2*t^2, -2*s^2, -2*(s^2+t^2)] ∧
      operatorB a = (fun j => 4*s*t*R j 2) ∧
      (dissipator (jump a) 1 = 0 ↔ t = 0) ∧
      (HasRotationAxis a ↔ t = 0 ∨ t = s) ∧
      (0 < t → t < s → ∀ U : Mat, IsRotation U →
        (Stabilizes a U ↔ U = 1 ∨ U = (2 • Matrix.of (fun i j => R i 2 * R j 2) - 1))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P59

end
