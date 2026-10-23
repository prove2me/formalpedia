-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_classical_index_eight_properties
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.classical_index_eight_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:32:40.422866+00:00
-- url     : https://prove2.me/theorems/fab0f8bb-0a05-4b04-9aa4-012158e5d6cc
-- title:
--   Proposition 35
-- statement:
--   For all positive dimensions, let $\mu_{\rm CZ}$ be the integer index constructed by the degree of the squared rotation map on an admissible extension. A path $\gamma:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$ is admissible when it is continuous, starts at $I$, and ends with $\det(\gamma(1)-I)\ne0$. All eight properties hold:
--
--   1. For every continuous symplectic path $\phi$ with arbitrary endpoints, $\mu_{\rm CZ}(\phi\gamma\phi^{-1})=\mu_{\rm CZ}(\gamma)$.
--   2. The index is constant under continuous homotopies through admissible paths; the final endpoint may move within $\operatorname{Sp}^*$.
--   3. If $\gamma(t)$ has no unit-circle eigenvalue for every $0<t\le1$, then $\mu_{\rm CZ}(\gamma)=0$.
--   4. For admissible paths $\gamma$ and $\eta$ in dimensions $2n$ and $2m$, with $n,m\ge1$, $\mu_{\rm CZ}(\gamma\oplus\eta)=\mu_{\rm CZ}(\gamma)+\mu_{\rm CZ}(\eta)$, using the grouped symplectic direct sum.
--   5. If $\phi(0)=\phi(1)=I$, then $\mu_{\rm CZ}(\phi\gamma)=\mu_{\rm CZ}(\gamma)+2\deg(\rho\circ\phi)$.
--   6. For a real symmetric nonsingular $2n$ by $2n$ matrix $S$ whose eigenvalues have absolute value less than $2\pi$, $2\mu_{\rm CZ}(t\mapsto e^{tJ_0S})=\operatorname{Sign}S$.
--   7. The endpoint parity is
--
--   $$(-1)^{n-\mu_{\rm CZ}(\gamma)}=\operatorname{sign}\det(I-\gamma(1)).$$
--
--   8. For pointwise matrix inversion and transpose, $\mu_{\rm CZ}(\gamma^{-1})=\mu_{\rm CZ}(\gamma^T)=-\mu_{\rm CZ}(\gamma)$.
--
--   Here $J_0=\left(\begin{smallmatrix}0&-I\\I&0\end{smallmatrix}\right)$, $\rho$ is the spectral rotation map, and $\operatorname{Sign}$ is positive minus negative inertia. These rules are conclusions about the constructed index, not assumptions defining a competing assignment.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 36, Proposition 35

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 35 ([11]), PDF pp.36–40: all eight properties of the
constructed integer index. Inverse and transpose are pointwise, conjugating
paths have arbitrary endpoints, and product compares positive dimensions. -/
theorem classical_index_eight_properties :
    (∀ n, 1 ≤ n → ∀ p phi : ℝ → GroupedRealMatrix n,
      IsAdmissible p 1 → IsPath phi 1 →
      conleyZehnder (fun t => phi t*p t*(phi t)⁻¹) 1 = conleyZehnder p 1) ∧
    (∀ n, 1 ≤ n → ∀ p q : ℝ → GroupedRealMatrix n,
      IsAdmissible p 1 → IsAdmissible q 1 → AdmissiblyHomotopic p q →
      conleyZehnder p 1 = conleyZehnder q 1) ∧
    (∀ n, 1 ≤ n → ∀ p : ℝ → GroupedRealMatrix n, IsAdmissible p 1 →
      (∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ eigenvalues (p t), ‖z‖ ≠ 1) →
      conleyZehnder p 1 = 0) ∧
    (∀ n m, 1 ≤ n → 1 ≤ m → ∀ p : ℝ → GroupedRealMatrix n,
      ∀ q : ℝ → GroupedRealMatrix m, IsAdmissible p 1 → IsAdmissible q 1 →
      conleyZehnder (fun t => symplecticSum (p t) (q t)) 1 =
        conleyZehnder p 1 + conleyZehnder q 1) ∧
    (∀ n, 1 ≤ n → ∀ p phi : ℝ → GroupedRealMatrix n,
      IsAdmissible p 1 → IsPath phi 1 → phi 0 = 1 → phi 1 = 1 →
      conleyZehnder (fun t => phi t*p t) 1 = conleyZehnder p 1 +
        2*winding (fun t => spectralRotation (phi t)) 1) ∧
    (∀ n, 1 ≤ n → ∀ S : GroupedRealMatrix n, IsSmallSymmetric S → S.det ≠ 0 →
      2*conleyZehnder (exponentialPath S) 1 = matrixSignature S) ∧
    (∀ n, 1 ≤ n → ∀ p : ℝ → GroupedRealMatrix n, IsAdmissible p 1 →
      (-1 : ℝ)^((n : ℤ)-conleyZehnder p 1) = Real.sign ((1-p 1).det)) ∧
    (∀ n, 1 ≤ n → ∀ p : ℝ → GroupedRealMatrix n, IsAdmissible p 1 →
      conleyZehnder (fun t => (p t)⁻¹) 1 = conleyZehnder (fun t => (p t).transpose) 1 ∧
      conleyZehnder (fun t => (p t).transpose) 1 = -conleyZehnder p 1) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
