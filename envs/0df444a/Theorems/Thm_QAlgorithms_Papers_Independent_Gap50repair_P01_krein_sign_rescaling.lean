-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_krein_sign_rescaling
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.krein_sign_rescaling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:16:44.985337+00:00
-- url     : https://prove2.me/theorems/b9ca52b6-4ee4-4827-a6a9-9bfab1874770
-- title:
--   Remark 11
-- statement:
--   Let $A\in\operatorname{Sp}(2,\mathbb R)$, and let $z=v-iw\ne0$ be an eigenvector for a nonreal eigenvalue $\lambda\in S^1$, with $v,w\in\mathbb R^2$. Then $\Omega_0(v,w)\ne0$ and every nonzero eigenvector of the same eigenvalue gives the same sign. For $a,b\in\mathbb R$ with $a^2+b^2>0$,
--
--   $$\Omega_0(av+bw,-bv+aw)=(a^2+b^2)\Omega_0(v,w),\qquad \Omega_{0,\mathbb C}(z,\overline z)=2i\Omega_0(v,w).$$
--
--   Complex conjugation produces an eigenvector for $\overline\lambda$ and reverses this sign. This makes the Krein-positive eigenvalue independent of the eigenvector chosen; the complex extension of $\Omega_0$ itself is bilinear.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 10, Remark 11

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Remark 11, PDF p.10: all eigenvectors have the same Krein sign;
nonzero rescaling preserves it and conjugation reverses it. -/
theorem krein_sign_rescaling (A : GroupedRealMatrix 1) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hzr : z.im ≠ 0) (v w : Coord 1 → ℝ)
    (he : (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0)
    (hev : (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
      z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))) :
    omegaR v w ≠ 0 ∧
    (∀ a b : ℝ, 0 < a^2+b^2 →
      omegaR (a • v+b • w) ((-b) • v+a • w) = (a^2+b^2)*omegaR v w ∧
      Real.sign (omegaR (a • v+b • w) ((-b) • v+a • w)) = Real.sign (omegaR v w)) ∧
    (∀ v2 w2 : Coord 1 → ℝ,
      (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) ≠ 0 →
      (complexify A).mulVec (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) =
        z • (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) →
      Real.sign (omegaR v2 w2) = Real.sign (omegaR v w)) ∧
    (complexify A).mulVec (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) =
      (star z) • (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) ∧
    omegaR v (-w) = -omegaR v w ∧
    omegaC (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))
      (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) = 2*Complex.I*(omegaR v w : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
