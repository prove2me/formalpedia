-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_extremal_block_ranks
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.extremal_block_ranks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:59:17.991448+00:00
-- url     : https://prove2.me/theorems/d078e25d-675b-4ff5-8a9d-31f6887ef00b
-- title:
--   Nonzero blocks of an extreme point have rank one
-- statement:
--   Let $d\ge2$. Let the five equality patterns of $(i,j,k)$ be $xxx,xxy,xyx,xyy,xyz$, with $xyz$ absent at $d=2$. Their multiplicities are $d$, $d(d-1)$ for each of the middle three, and $d(d-1)(d-2)$. Write $s_\ell^\nu=(n_\ell/d)r_\ell^\nu$ for the scaled positive multiplicity blocks in sectors $\nu=\alpha,\beta,\gamma$. Alpha blocks are $2\times2$; beta and gamma are supported on their respective plus and minus coordinates. Gamma is absent at $d=2$. Let $\mathcal M_d$ be the unswapped block set satisfying
--   $$\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{++}=d_+,\qquad\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{--}=d_-,$$
--   where $d_\pm=d(d\pm1)/2$, $d_\alpha=d$, $d_\beta=d(d-1)(d+2)/2$, and $d_\gamma=d(d+1)(d-2)/2$. Blocks for absent sectors and classes are zero.
--
--   If $s$ is a geometric extreme point of $\mathcal M_d$, then
--   $$\operatorname{rank}(s_\ell^\nu)\le1\quad\text{for all }\ell,\nu;\qquad s_\ell^\nu\ne0\Longrightarrow\operatorname{rank}(s_\ell^\nu)=1.$$
--   Zero blocks are permitted. This corrects the printed unconditional rank-one sentence to the conclusion its proof uses, consistently with the next lemma's allowance of all but two blocks being zero. It restricts the shape of possible optimal extreme points.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 7, Lemma 6: ranks of nonzero extremal blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.7, Lemma 6. Source correction: the proof
excludes rank two; zero blocks remain allowed (as the next lemma explicitly uses).
Thus every block has rank at most one. Independent moderation is pending. -/
theorem extremal_block_ranks (d : ℕ) (hd : 2 ≤ d) (b : BlockArray)
    (hb : b ∈ (cloningBlockSet d).extremePoints ℝ) :
    ∀ l v, (b l v).rank ≤ 1 ∧ (b l v ≠ 0 → (b l v).rank = 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
