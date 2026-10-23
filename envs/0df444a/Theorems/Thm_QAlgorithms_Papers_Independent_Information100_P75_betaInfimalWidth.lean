-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_betaInfimalWidth
-- name    : QAlgorithms.Papers.Independent.Information100.P75.betaInfimalWidth
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:17:49.098852+00:00
-- url     : https://prove2.me/theorems/9f8e776f-30e7-4dfa-a19d-ab303a24d89d
-- title:
--   Explicit infimal width of the conjecture subspace
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   For $\pi/2\le\beta\le\pi$, let $S_\beta=\operatorname{span}_{\mathbb C}\{\operatorname{diag}(1,e^{i\beta},0),\operatorname{diag}(0,1,e^{i\beta})\}$. Then
--
--   $$\operatorname{sw}^*(S_\beta)=2\beta-\pi.$$
--
--   The endpoint widths are $0$ at $\beta=\pi/2$ and $\pi$ at $\beta=\pi$. This computes an infimum and does not assert that any matrix attains it.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 9, Appendix D

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Appendix D, PDF p.9: the computed infimal width, including both endpoints.
No matrix attaining the infimum is asserted. -/
theorem betaInfimalWidth (b : ℝ) (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    infWidth (betaSpace b) = 2 * b - Real.pi := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
