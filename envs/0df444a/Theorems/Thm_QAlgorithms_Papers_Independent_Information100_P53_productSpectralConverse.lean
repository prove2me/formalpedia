-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_productSpectralConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P53.productSpectralConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:01:08.356638+00:00
-- url     : https://prove2.me/theorems/0fc9ec87-27b2-4480-ac9f-200079053262
-- title:
--   Proposition-1
-- statement:
--   Let $n\ge1$, let $\mathbb F$ be a finite field of cardinality $q\ge2$, and let $\rho_x$ ($x\in\mathbb F$) be density operators on $\mathbb C^q$. For each symbol choose a decreasing spectrum $a_{x,j}$ and complete orthonormal eigenbasis $|a_{x,j}\rangle$. Let $C=(x_m)_{m=1}^M$ enumerate $M\ge1$ distinct words in $\mathbb F^n$. Its quantum codeword is $\rho_{x_m}=\bigotimes_{l=1}^n\rho_{x_{m,l}}$, and its eigenvector labels are the tuples $\mathbf j\in\{1,\ldots,q\}^n$.
--
--   Fix $p_m\ge0$ with $\sum_m p_m=1$. Let $I$ contain $q^n$ pairs $(m,\mathbf j)$ whose weights $p_m\prod_l a_{x_{m,l},j_l}$ dominate all unselected weights, including arbitrary tie choices. Then
--   $$P_c(p,S_C)\le\sum_{(m,\mathbf j)\in I}p_m\prod_{l=1}^na_{x_{m,l},j_l}.$$
--
--   The decoder alone is optimized; no uniform prior, code linearity, or symbol symmetry is required.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, Proposition-1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.5, Proposition 1: optimized spectral converse for product-state codewords,
with arbitrary prior and no linearity, distance, or channel symmetry assumption.
Printed: Section III-C places single-use symbols in D(H_q^{tensor n}).
Changed: single-use states act on H_q. Why: the q spectral labels and n-factor
codeword construction require this single-use dimension. -/
theorem productSpectralConverse {n q M : ℕ} (hn : 0 < n) (hq2 : 2 ≤ q)
    (hM : 0 < M) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : Fintype.card F = q) (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a)) (s : ∀ a, SpectralData (rho a))
    (code : Fin M → Fin n → F) (hcode : Function.Injective code)
    (p : Fin M → ℝ) (hp : IsPrior p) (I : Finset (Fin M × (Fin n → Fin q)))
    (hI : IsTopSelection (q ^ n) (productWeight p (fun a => (s a).value) code) I) :
    mixedOptSuccess p (fun m => productMatrix rho (code m)) ≤
      ∑ z ∈ I, productWeight p (fun a => (s a).value) code z := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
