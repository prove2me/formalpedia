-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_paninski_chi_squared_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.paninski_chi_squared_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:58:54.103994+00:00
-- url     : https://prove2.me/theorems/eb8197e4-f72e-4838-93ce-c52e5ae8196b
-- title:
--   Theorem 4.2
-- statement:
--   For even $d\ge2$, $n\ge0$, and $0\le\epsilon\le1/2$, let $P_d^\epsilon$ alternate probabilities $(1+2\epsilon)/d$ and $(1-2\epsilon)/d$. Then
--
--   $$d_{\chi^2}(\mathrm{SW}_{P_d^\epsilon}^n,\mathrm{SW}_d^n)\le\exp((4n\epsilon^2/d)^2)-1.$$
--
--   The divergence is directed from the perturbed law to the uniform law. It vanishes for $\epsilon=0$ or $n=0$ and yields the mixedness testing lower bound.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 34, Theorem 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 4.2, arXiv:1501.05028v1, PDF p.34. Even dimension and perturbation nonnegativity are section assumptions. Direction of chi-squared is retained. -/
theorem paninski_chi_squared_bound
    (d n : ℕ) (hd : 0 < d) (heven : Even d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1/2) :
    chiSq (swSpectrum (n := n) (paninski d epsilon)) (swSpectrum (n := n) (unif d)) ≤
      Real.exp ((4*n*epsilon^2/d)^2) - 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
