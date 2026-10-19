-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_subset_concavity_and_increment
-- name    : QAlgorithms.Papers.Independent.Information100.P27.subset_concavity_and_increment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:20:09.843325+00:00
-- url     : https://prove2.me/theorems/03698cd0-6566-4310-a4fe-dc0dbe704a8d
-- title:
--   Lemma B.1: subset concavity and upper increment bound
-- statement:
--   Let $n\ge1$ and let $\omega_{XFA^n}=\sum_x p_x|x\rangle\langle x|\otimes\rho_x$ be a finite state classical on $X$. The states $\rho_x$ on arbitrary memory $F$ and systems $A_1,\ldots,A_n$ need not be pure or independent, and the systems need not have equal dimensions. For a subset $J\subseteq[n]$, use the one-dimensional empty product when $J=\varnothing$. Define the real polynomials $f(r)=\sum_Jr^{|J|}(1-r)^{n-|J|}H(A_J|X)$ and $g(r)=\sum_Jr^{|J|}(1-r)^{n-|J|}H(FA_J|X)$, and set $H_\Sigma=\sum_iH(A_i)_\omega$ using unconditional single-site marginals. Both $f$ and $g$ are concave on $[0,1]$, and
--
--   $$
--   f'(r)\le H_\Sigma\quad(0\le r\le1),\qquad f(v)-f(u)\le(v-u)H_\Sigma\quad(0\le u\le v\le1).
--   $$
--
--   The derivative is that of the full real polynomial, including at endpoints. This is an upper increment bound and does not assert monotonicity.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 58, Lemma B.1: subset concavity and upper increment bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF pp.57-59, Lemma B.1: subset concavity and upper
increment bound for arbitrary, potentially unequal and correlated, systems. -/
theorem subset_concavity_and_increment {n f m : ℕ} (hn : 0 < n) (hf : 0 < f)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ)
    (hp : IsProbability p) (hrho : ∀ x, IsDensityMatrix (rho x)) :
    ConcaveOn ℝ (Set.Icc 0 1) (subsetPolynomial p rho false) ∧
    ConcaveOn ℝ (Set.Icc 0 1) (subsetPolynomial p rho true) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) 1,
      deriv (subsetPolynomial p rho false) r ≤ singleEntropySum p rho) ∧
    (∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      subsetPolynomial p rho false v - subsetPolynomial p rho false u ≤
        (v-u) * singleEntropySum p rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
