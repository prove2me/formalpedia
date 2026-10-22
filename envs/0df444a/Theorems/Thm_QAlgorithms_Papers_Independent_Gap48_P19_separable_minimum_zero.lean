-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_separable_minimum_zero
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.separable_minimum_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:09:18.144935+00:00
-- url     : https://prove2.me/theorems/c0271df0-c311-4c0a-adb1-9ed9f1bda223
-- title:
--   A product-flag extension attains the zero quantum minimum
-- statement:
--   Let $\rho_{AB}=\sum_{l=1}^{n}w_l\rho_A^l\otimes\rho_B^l$, with $n\ge1$, normalized nonnegative weights, and density-matrix components on nonzero finite spaces. For any orthonormal flag basis, construct $\omega_{ABL}$ by (7). It is a valid extension of $\rho_{AB}$. If $K_0(\rho)$ is the set of all density-matrix extensions with arbitrary positive finite auxiliary dimension, then
--
--   $$\min_{\tau\in K_0(\rho)}I_\tau(A:B\mid L)=0.$$
--
--   This minimum is attained by the displayed construction. Every class of valid extensions containing that construction likewise has attained minimum zero. The result supplies the optimizer from the product decomposition.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 4, §2, Eq.(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (8): the computed product-flag extension attains zero in K0,
and in every valid class containing it. Nonnegative CMI corrects printed (4). -/
theorem separable_minimum_zero {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ) (ra : Fin n → Mat A) (rb : Fin n → Mat B)
    (F : Matrix.unitaryGroup (Fin n) ℂ) (hw : IsLaw w)
    (ha : ∀ l, IsDensityMatrix (ra l)) (hb : ∀ l, IsDensityMatrix (rb l)) :
    let rho := ∑ l, (w l : ℂ) • Matrix.kronecker (ra l) (rb l)
    let e : QuantumExtension A B := ⟨n, flaggedProduct w ra rb F⟩
    ValidQuantum rho e ∧ IsLeast (quantumScores rho) 0 ∧
      ∀ K : Set (QuantumExtension A B),
        (∀ f ∈ K, ValidQuantum rho f) → e ∈ K →
        IsLeast {r | ∃ f ∈ K, extensionQuantumCMI f.2 = r} 0 := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
