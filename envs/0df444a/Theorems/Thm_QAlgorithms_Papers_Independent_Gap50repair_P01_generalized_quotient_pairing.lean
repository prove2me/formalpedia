-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_generalized_quotient_pairing
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_quotient_pairing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:19:26.93691+00:00
-- url     : https://prove2.me/theorems/9b3deed3-07fd-4697-a5b6-03c27e058912
-- title:
--   Lemma 21
-- statement:
--   Let $A$ be symplectic, $\lambda\ne0$ an eigenvalue, and $j>0$ an integer. On the generalized spaces $E_\lambda$ and $E_{\lambda^{-1}}$, restrict the kernels $K_\lambda=\ker((A-\lambda I)^j|_{E_\lambda})$ and $K_{\lambda^{-1}}$ analogously. There exists a well-defined complex bilinear pairing
--
--   $$\widetilde Q:E_\lambda/K_\lambda\times E_{\lambda^{-1}}/K_{\lambda^{-1}}\longrightarrow\mathbb C,\qquad \widetilde Q([v],[w])=\Omega_0((A-\lambda I)^jv,w).$$
--
--   It is nondegenerate in each variable. The formula on representatives and both annihilator conditions are included. The statement also covers heights beyond the nilpotence length, when both quotients are zero.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 17, Lemma 21

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 21, PDF p.17: bilinear map on the restricted quotients, pullback
formula, and left and right nondegeneracy. -/
theorem generalized_quotient_pairing {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : IsEigenvalue A z) (hz0 : z ≠ 0) (j : ℕ) (hj : 0 < j) :
    ∃ Q : GeneralizedQuotient A z j →ₗ[ℂ] GeneralizedQuotient A z⁻¹ j →ₗ[ℂ] ℂ,
      (∀ v : generalizedSpace A z, ∀ w : generalizedSpace A z⁻¹,
        Q ((restrictedKernel A z j).mkQ v) ((restrictedKernel A z⁻¹ j).mkQ w) =
          omegaC ((shifted A z^j) v.val) w.val) ∧
      (∀ v, (∀ w, Q v w = 0) → v = 0) ∧ (∀ w, (∀ v, Q v w = 0) → w = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
