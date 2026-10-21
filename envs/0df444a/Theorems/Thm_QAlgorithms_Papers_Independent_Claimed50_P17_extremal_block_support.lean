-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_extremal_block_support
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.extremal_block_support
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:59:53.705473+00:00
-- url     : https://prove2.me/theorems/bd91d943-95ca-43bb-8432-6d9e3145bfbd
-- title:
--   At most two nonzero sector-class blocks at an extreme point
-- statement:
--   Let $d\ge2$. Let the five equality patterns of $(i,j,k)$ be $xxx,xxy,xyx,xyy,xyz$, with $xyz$ absent at $d=2$. Their multiplicities are $d$, $d(d-1)$ for each of the middle three, and $d(d-1)(d-2)$. Write $s_\ell^\nu=(n_\ell/d)r_\ell^\nu$ for the scaled positive multiplicity blocks in sectors $\nu=\alpha,\beta,\gamma$. Alpha blocks are $2\times2$; beta and gamma are supported on their respective plus and minus coordinates. Gamma is absent at $d=2$. Let $\mathcal M_d$ be the unswapped block set satisfying
--   $$\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{++}=d_+,\qquad\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{--}=d_-,$$
--   where $d_\pm=d(d\pm1)/2$, $d_\alpha=d$, $d_\beta=d(d-1)(d+2)/2$, and $d_\gamma=d(d+1)(d-2)/2$. Blocks for absent sectors and classes are zero.
--
--   For every geometric extreme point $s$ of $\mathcal M_d$,
--   $$\#\{(\ell,\nu):s_\ell^\nu\ne0\}\le2.$$
--   The count is of entire sector-class blocks. Absent sectors and classes contribute zero. This limits the support of the extreme-point search used for cloning.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 7, Lemma 7: support of extremal blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.7, Lemma 7: at most two nonzero
(sector,class) blocks at a geometric extreme point. Absent gamma blocks are zero. -/
theorem extremal_block_support (d : ℕ) (hd : 2 ≤ d) (b : BlockArray)
    (hb : b ∈ (cloningBlockSet d).extremePoints ℝ) :
    (blockSupport b).card ≤ 2 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
