-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_subset_midpoint
-- name    : QAlgorithms.Papers.Independent.Information100.P27.subset_midpoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:20:51.185714+00:00
-- url     : https://prove2.me/theorems/2b118b63-8169-4e2a-9e7e-c0bd0f38a12b
-- title:
--   Lemma B.2: midpoint subset inequality
-- statement:
--   Let $n\ge1$ and let $\omega_{XFA^n}=\sum_xp_x|x\rangle\langle x|\otimes\rho_x$ be a normalized finite state classical on $X$, with arbitrary quantum memory $F$ and arbitrary, possibly unequal, component systems. Define $f(r)=\sum_{J\subseteq[n]}r^{|J|}(1-r)^{n-|J|}H(A_J|X)$ and $g(r)=\sum_{J\subseteq[n]}r^{|J|}(1-r)^{n-|J|}H(FA_J|X)$, with a one-dimensional empty product. Then
--
--   $$
--   g(1/2)\ge f(1/2).
--   $$
--
--   No purity, independence, or erasure-model assumption is required. This midpoint inequality supplies the endpoint used in subset interpolation.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 59, Lemma B.2: midpoint subset inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF pp.57,59, Lemma B.2: midpoint inequality with
arbitrary quantum memory and a classical conditioning register. -/
theorem subset_midpoint {n f m : ℕ} (hn : 0 < n) (hf : 0 < f)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ)
    (hp : IsProbability p) (hrho : ∀ x, IsDensityMatrix (rho x)) :
    subsetPolynomial p rho false (1/2) ≤ subsetPolynomial p rho true (1/2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
