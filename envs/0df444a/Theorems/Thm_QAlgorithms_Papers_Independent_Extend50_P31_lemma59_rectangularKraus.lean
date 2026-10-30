-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma59_rectangularKraus
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma59_rectangularKraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:04:32.496681+00:00
-- url     : https://prove2.me/theorems/836f2a39-2b90-486f-8ba2-0b0c35ad55d2
-- title:
--   Appendix D, Lemma 59: Choi eigenvectors give a normalized Kraus family
-- statement:
--   Let $d,e>0$ and let $\Phi:M_d(\mathbb C)\to M_e(\mathbb C)$ be CPTP. Let $x_m$ be a complete orthonormal eigenbasis of its unnormalized input-first Choi matrix, with eigenvalues $\lambda_m\ge0$, including zeros. Row unvectorization gives an input-by-output matrix $X_m\in M_{d\times e}(\mathbb C)$. Then
--
--   $$
--   K_m=\sqrt{\lambda_m}\,X_m^T\in M_{e\times d}(\mathbb C),\qquad\Phi(X)=\sum_mK_mXK_m^\dagger,\qquad\sum_mK_m^\dagger K_m=I_d.
--   $$
--
--   This converts a complete normalized Choi eigensystem to a normalized Kraus representation on every input operator, including rectangular channels.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 40, Appendix D, Lemma 59: Choi eigenvectors give a normalized Kraus family

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- Appendix D, Lemma 59 PDF pp.40--41 Eqs.(196),(200)--(203).
Input dimension d and output dimension e are independently positive. Zero eigenvalues are retained. -/
theorem lemma59_rectangularKraus (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (Phi : Mat d →ₗ[ℂ] Mat e) (hch : IsPaperChannel Phi)
    (x : Fin (d*e) → (Fin d × Fin e) → ℂ) (lambda : Fin (d*e) → ℝ)
    (hnonneg : ∀ m, 0 ≤ lambda m)
    (horth : ∀ m k, (∑ p, conj (x m p) * x k p) = if m = k then 1 else 0)
    (hspan : Submodule.span ℂ (Set.range x) = ⊤)
    (heigen : ∀ m, (choi Phi).mulVec (x m) = (lambda m : ℂ) • x m) :
    let K : Fin (d*e) → Matrix (Fin e) (Fin d) ℂ :=
      fun m => (Real.sqrt (lambda m) : ℂ) • (rowVec.symm (x m))ᵀ
    QAlgorithms.IsKrausFamily K ∧ ∀ X : Mat d, Phi X = QAlgorithms.krausApply K X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
