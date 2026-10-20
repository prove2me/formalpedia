-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_choi_tests
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.choi_tests
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:49:33.321234+00:00
-- url     : https://prove2.me/theorems/0827fc97-9e9f-48d3-971e-3c909871f1f6
-- title:
--   Equation (A8): attained Choi test programs
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be any physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Let $J_E=d_{\rm in}(\operatorname{id}\otimes E)(\psi_+)$ be the unnormalized Choi matrix, with $\psi_+$ normalized. Let $\rho$ range over density matrices on the input space. Joint optimization over $\rho,Q,\lambda$ gives
--   $$
--   \begin{aligned}
--   R_{H,\mathcal O}^\epsilon(E)^{-1}
--   &=\min\{\lambda:0\le Q\le\rho\otimes I,\ \langle Q,J_E\rangle\ge1-\epsilon,\ \langle Q,J_M\rangle\le\lambda\ \forall M\in\mathcal O\},\\
--   R_{H,\operatorname{aff}(\mathcal O)}^\epsilon(E)^{-1}
--   &=\min\{\lambda:0\le Q\le\rho\otimes I,\ \langle Q,J_E\rangle\ge1-\epsilon,\ \langle Q,J_M\rangle=\lambda\ \forall M\in\mathcal O\}.
--   \end{aligned}
--   $$
--   Both minima have attaining triples. These forms make the testing quantities accessible to convex optimization.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 9, Equation (A8): attained Choi test programs

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Eq.(A8), PDF p.9: both Choi testing identities with attaining triples.
J has trace din. The following purification sentence in the source suppresses
a dimension factor for normalized psiPlus; this statement uses (A8) itself. -/
theorem choi_tests (O : ResourceTheory) (hO : Regular O) {p : Port}
    (E : ChannelChoi p) (hE : E ∈ O.allowed p) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    IsLeast (choiTestValues O E e false) ((testing O E e)⁻¹) ∧
    IsLeast (choiTestValues O E e true) ((testingAffine O E e)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
