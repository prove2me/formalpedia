-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_extremality_criterion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.extremality_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:58:23.083293+00:00
-- url     : https://prove2.me/theorems/825eb701-f931-41ce-bf34-07c4e1293b82
-- title:
--   Geometric extremality and positive-radius perturbations
-- statement:
--   Let $d\ge2$. Let the five equality patterns of $(i,j,k)$ be $xxx,xxy,xyx,xyy,xyz$, with $xyz$ absent at $d=2$. Their multiplicities are $d$, $d(d-1)$ for each of the middle three, and $d(d-1)(d-2)$. Write $s_\ell^\nu=(n_\ell/d)r_\ell^\nu$ for the scaled positive multiplicity blocks in sectors $\nu=\alpha,\beta,\gamma$. Alpha blocks are $2\times2$; beta and gamma are supported on their respective plus and minus coordinates. Gamma is absent at $d=2$. Let $\mathcal M_d$ be the unswapped block set satisfying
--   $$\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{++}=d_+,\qquad\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{--}=d_-,$$
--   where $d_\pm=d(d\pm1)/2$, $d_\alpha=d$, $d_\beta=d(d-1)(d+2)/2$, and $d_\gamma=d(d+1)(d-2)/2$. Blocks for absent sectors and classes are zero.
--
--   Fix $s\in\mathcal M_d$. A perturbation is a Hermitian array $z$ for which some $\epsilon>0$ satisfies $s+hz\in\mathcal M_d$ for every real $h\in[-\epsilon,\epsilon]$. Then
--   $$s\in\operatorname{Ext}(\mathcal M_d)\iff\text{every perturbation of }s\text{ is }0.$$
--   Extremality is geometric extremality in the real vector space of block arrays. The positive-radius correction is necessary: the printed condition $\epsilon\ge0$ permits $\epsilon=0$ and would make every Hermitian array a perturbation. This characterization is used for the following structural restrictions.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 7, §V, Definition 1 and following unnumbered extremality criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.7, Definition 1 and its extremality criterion.
Source correction: printed epsilon>=0 is replaced by epsilon>0, as required by
its subsequent two-sided-neighborhood argument. Independent moderation is pending. -/
theorem extremality_criterion (d : ℕ) (hd : 2 ≤ d) (b : BlockArray)
    (hb : b ∈ cloningBlockSet d) :
    b ∈ (cloningBlockSet d).extremePoints ℝ ↔
      ∀ z : BlockArray, IsPerturbation d b z → z = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
