-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_subset_interpolation
-- name    : QAlgorithms.Papers.Independent.Information100.P27.subset_interpolation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:21:27.918834+00:00
-- url     : https://prove2.me/theorems/d0a5ddc4-c11b-4600-899e-7c4854084b72
-- title:
--   Lemma B.3: subset interpolation with arbitrary quantum memory
-- statement:
--   Let $n\ge1$ and let $\omega_{XFA^n}=\sum_xp_x|x\rangle\langle x|\otimes\rho_x$ be a normalized finite state classical on $X$, with unrestricted quantum memory $F$ and arbitrary component dimensions. Put $f(r)=\sum_{J\subseteq[n]}r^{|J|}(1-r)^{n-|J|}H(A_J|X)$, $g(r)=\sum_{J\subseteq[n]}r^{|J|}(1-r)^{n-|J|}H(FA_J|X)$, $f_F=H(F|X)$, and $H_\Sigma=\sum_iH(A_i)_\omega$. For $0\le r\le1/2$,
--
--   $$
--   g(r)\ge2r f(1-r)+(1-2r)f_F-r(1-2r)H_\Sigma.
--   $$
--
--   All conditional entropies are averages over the classical label. The negative correction and arbitrary quantum memory are retained, including both endpoints.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 59, Lemma B.3: subset interpolation with arbitrary quantum memory

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF pp.57,59-60, Lemma B.3: interpolation retaining the
negative correction and unrestricted finite quantum memory. -/
theorem subset_interpolation {n f m : ℕ} (hn : 0 < n) (hf : 0 < f)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ)
    (hp : IsProbability p) (hrho : ∀ x, IsDensityMatrix (rho x))
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    2*r * subsetPolynomial p rho false (1-r) +
      (1-2*r) * conditionalMemoryEntropy p rho - r*(1-2*r) * singleEntropySum p rho ≤
      subsetPolynomial p rho true r := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
