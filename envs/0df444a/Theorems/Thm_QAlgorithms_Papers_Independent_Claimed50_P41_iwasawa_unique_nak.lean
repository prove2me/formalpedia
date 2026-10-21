-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_iwasawa_unique_nak
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.iwasawa_unique_nak
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:02:57.613244+00:00
-- url     : https://prove2.me/theorems/117d27ee-d2e5-444c-826f-4a1051d52162
-- title:
--   §IV (4.22)–(4.24): unique Iwasawa NAK decomposition
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let N consist of matrices $\begin{pmatrix}A&0\\C&A^{-T}\end{pmatrix}$ with A lower unitriangular and A transpose times C symmetric, and let the positive diagonal subgroup be D(kappa).
--
--   $$
--   \forall S\in\mathrm{Sp},\quad\exists! (N_0,D,K_0),\quad S=N_0DK_0.
--   $$
--
--   The dimensions of N, the positive diagonal group and K are n squared, n, n squared. In one mode the theorem also gives xi=(ac+bd)/(a squared+b squared), eta=log(a squared+b squared), phi=2 arg(a-i b) in (-2 pi,2 pi], with the displayed rotation having upper-right entry -sin(phi/2). The first-row squared norm is strictly positive.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 18, §IV (4.22)–(4.24): unique Iwasawa NAK decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.17–18, (4.22)–(4.24): unique NAK factors, with the explicit
one-mode formulas and the source argument branch (-2pi,2pi]. -/
theorem iwasawa_unique_nak (n : ℕ) (hn : 0 < n) :
    (∀ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S →
      ∃! f : Matrix (Phase n) (Phase n) ℝ × (Fin n → ℝ) × Matrix (Phase n) (Phase n) ℝ,
        IsNilpotentFactor f.1 ∧ (∀ i, 0 < f.2.1 i) ∧ IsPassive f.2.2 ∧
          S = f.1 * squeezeMatrix f.2.1 * f.2.2) ∧
    (∀ S : Matrix (Phase 1) (Phase 1) ℝ, PreservesCanonicalForm S →
      let a := S (Sum.inl 0) (Sum.inl 0)
      let b := S (Sum.inl 0) (Sum.inr 0)
      let c := S (Sum.inr 0) (Sum.inl 0)
      let d := S (Sum.inr 0) (Sum.inr 0)
      let xi := (a * c + b * d) / (a ^ 2 + b ^ 2)
      let eta := Real.log (a ^ 2 + b ^ 2)
      let phi := 2 * Complex.arg ((a : ℂ) - Complex.I * (b : ℂ))
      0 < a ^ 2 + b ^ 2 ∧ -2 * Real.pi < phi ∧ phi ≤ 2 * Real.pi ∧
      S = lensMatrix (fun _ _ => xi) * squeezeMatrix (fun _ => Real.exp (eta / 2)) *
        passiveMatrix (fun _ _ => Real.cos (phi / 2)) (fun _ _ => -Real.sin (phi / 2))) ∧
    dimH {N : Matrix (Phase n) (Phase n) ℝ | IsNilpotentFactor N} = (n ^ 2 : ℕ) ∧
    dimH {D : Matrix (Phase n) (Phase n) ℝ | ∃ kappa, (∀ i, 0 < kappa i) ∧ D = squeezeMatrix kappa} = n ∧
    dimH {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} = (n ^ 2 : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
