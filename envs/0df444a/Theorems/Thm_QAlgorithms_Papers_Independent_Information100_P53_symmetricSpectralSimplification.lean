-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_symmetricSpectralSimplification
-- name    : QAlgorithms.Papers.Independent.Information100.P53.symmetricSpectralSimplification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:02:36.189237+00:00
-- url     : https://prove2.me/theorems/055d60ef-5698-4128-931d-66ea071d6463
-- title:
--   symmetric-spectral-simplification
-- statement:
--   Let $n\ge1$, let $\mathbb F$ be a finite field of cardinality $q\ge2$, and let $\rho_x$ ($x\in\mathbb F$) be density operators on $\mathbb C^q$. For each symbol choose a decreasing spectrum $a_{x,j}$ and complete orthonormal eigenbasis $|a_{x,j}\rangle$. Let $C=(x_m)_{m=1}^M$ enumerate $M\ge1$ distinct words in $\mathbb F^n$. Its quantum codeword is $\rho_{x_m}=\bigotimes_{l=1}^n\rho_{x_{m,l}}$, and its eigenvector labels are the tuples $\mathbf j\in\{1,\ldots,q\}^n$.
--
--   Suppose every pair of symbol states is related by unitary conjugation, and use uniform message probabilities $1/M$. Fix any reference symbol $x_*$. Let $I$ select the $q^n$ largest weights $M^{-1}\prod_l a_{x_{m,l},j_l}$, and let $J$ select the $q^n$ largest entries of the multiset of $M$ copies of $M^{-1}\prod_l a_{x_*,j_l}$, with any tie resolutions. Then
--   $$\sum_{(m,\mathbf j)\in I}\frac1M\prod_la_{x_{m,l},j_l}
--   =\sum_{(m,\mathbf j)\in J}\frac1M\prod_la_{x_*,j_l}.$$
--
--   Hence the bound depends on the code through $n,q,M$ and on the common symbol spectrum; it is independent of the particular codewords. No runtime statement is included.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 5, symmetric-spectral-simplification

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.5, §III-D structural simplification under Definition 2: with uniform
prior the top q^n weighted eigenvalues are obtained from M copies of one common
product spectrum. This statement makes no computational runtime claim. -/
theorem symmetricSpectralSimplification {n q M : ℕ} (hn : 0 < n) (hq2 : 2 ≤ q)
    (hM : 0 < M) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a)) (s : ∀ a, SpectralData (rho a))
    (hsym : IsSymmetric rho) (code : Fin M → Fin n → F)
    (hcode : Function.Injective code) (reference : F)
    (I J : Finset (Fin M × (Fin n → Fin q)))
    (hI : IsTopSelection (q ^ n)
      (productWeight (fun _ => 1 / (M : ℝ)) (fun a => (s a).value) code) I)
    (hJ : IsTopSelection (q ^ n)
      (fun z : Fin M × (Fin n → Fin q) =>
        (1 / (M : ℝ)) * ∏ l, (s reference).value (z.2 l)) J) :
    (∑ z ∈ I, productWeight (fun _ => 1 / (M : ℝ)) (fun a => (s a).value) code z) =
      ∑ z ∈ J, (1 / (M : ℝ)) * ∏ l, (s reference).value (z.2 l) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
