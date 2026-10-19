-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_productEigenbasis
-- name    : QAlgorithms.Papers.Independent.Information100.P53.productEigenbasis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:00:36.00621+00:00
-- url     : https://prove2.me/theorems/1e1a29f1-da42-48e2-b483-33624c30e2c4
-- title:
--   Lemma-4
-- statement:
--   Let $n\ge1$, let $\mathbb F$ be a finite field of cardinality $q\ge2$, and let $\rho_x$ ($x\in\mathbb F$) be density operators on $\mathbb C^q$. For each symbol choose a decreasing spectrum $a_{x,j}$ and complete orthonormal eigenbasis $|a_{x,j}\rangle$. Eigenvector labels are the tuples $\mathbf j\in\{1,\ldots,q\}^n$.
--
--   For any word $x\in\mathbb F^n$ define $v_{\mathbf j}=\bigotimes_{l=1}^n|a_{x_l,j_l}\rangle$. Then
--   $$\left(\bigotimes_{l=1}^n\rho_{x_l}\right)v_{\mathbf j}
--   =\left(\prod_{l=1}^na_{x_l,j_l}\right)v_{\mathbf j}.$$
--   The vectors $v_{\mathbf j}$ form a complete orthonormal basis and give the reconstruction
--   $$\bigotimes_l\rho_{x_l}=\sum_{\mathbf j}\left(\prod_la_{x_l,j_l}\right)|v_{\mathbf j}\rangle\langle v_{\mathbf j}|.$$
--
--   This identifies the entire tensor-product spectrum with multiplicity, rather than just individual eigenpairs.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, Lemma-4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF pp.4–5, Lemma 4: tensor eigenvalue equation and complete orthonormal
eigenbasis, including reconstruction.
Printed: Section III-C places single-use symbols in D(H_q^{tensor n}).
Changed: single-use states act on H_q. Why: its q spectral labels and the n-factor
construction in Sections II-C and III-C require single-use dimension q. -/
theorem productEigenbasis {n q : ℕ} (hn : 0 < n) {F : Type*} [Field F] [Fintype F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a)) (s : ∀ a, SpectralData (rho a))
    (x : Fin n → F) :
    (∀ j : Fin n → Fin q, act (productMatrix rho x) (productVector s x j) =
      ((∏ l, (s (x l)).value (j l) : ℝ) : ℂ) • productVector s x j) ∧
    (∃ B : OrthonormalBasis (Fin n → Fin q) ℂ (EuclideanSpace ℂ (Fin n → Fin q)),
      ∀ j, B j = productVector s x j) ∧
    productMatrix rho x = ∑ j : Fin n → Fin q,
      (((∏ l, (s (x l)).value (j l) : ℝ) : ℂ) • pureDensity (productVector s x j)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
