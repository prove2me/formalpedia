-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_young_sector_spectrum
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.young_sector_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:15:07.339408+00:00
-- url     : https://prove2.me/theorems/1fb93860-8b1d-4e00-9cb8-0c30de49ab8b
-- title:
--   Appendix B, unnumbered: Young-sector eigenvalue prescription
-- statement:
--   Let $d\ge2$, $m,n\ge1$, and $H=-(mn)^{-1}\sum_{i\in L,j\in R}V_{ij}$ on $(m+n)$ qudits. For a Young diagram $Y$ of size $N$ with at most $d$ rows, let $P_Y$ be its physical tensor-permutation isotypic projector, constructed by the character formula $P_Y=f_Y/N!\sum_{\pi\in S_N}\chi_Y(\pi^{-1})V_\pi$, where $f_Y$ and $\chi_Y$ are the dimension and character of the Specht module. For shapes $Y_L,Y_R,Y$ of sizes $m,n,m+n$ define $Q=P_Y(P_{Y_L}\otimes P_{Y_R})$, all on the same full register. Let $A_Y$ be the sum of squared column heights and $B_Y$ the sum of squared row lengths, and put
--   $$h(Y_L,Y_R,Y)=\frac{A_Y-A_{Y_L}-A_{Y_R}-B_Y+B_{Y_L}+B_{Y_R}}{2mn}.$$
--   The sectors sum to identity and each satisfies $HQ=h(Y_L,Y_R,Y)Q$. Exactly the nonzero sectors give the real spectrum:
--   $$\operatorname{spec}_{\mathbb R}(H)=\{h(Y_L,Y_R,Y):Q\ne0\}.$$
--   The nonzero-sector condition is determined by independent physical projectors, not by the desired eigenvalue formula.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 17, Appendix B, unnumbered: Young-sector eigenvalue prescription

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Eq.(B3), PDF pp.17–18: the exact real spectrum consists of the prescribed
Young scalars for nonzero independently constructed physical sectors; every such
sector is an eigenspace component and their sum is identity. -/
theorem young_sector_spectrum (d m n : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (hn : 0 < n) :
    (∑ YL : Schur.Partition d m, ∑ YR : Schur.Partition d n,
      ∑ Y : Schur.Partition d (m+n), youngSector YL YR Y) = 1 ∧
    (∀ (YL : Schur.Partition d m) (YR : Schur.Partition d n) (Y : Schur.Partition d (m+n)),
      sharingHamiltonian d m n * youngSector YL YR Y =
        (youngEigenvalue YL YR Y : ℂ) • youngSector YL YR Y) ∧
    realEigenvalues (sharingHamiltonian d m n) =
      {r | ∃ (YL : Schur.Partition d m) (YR : Schur.Partition d n) (Y : Schur.Partition d (m+n)),
        youngSector YL YR Y ≠ 0 ∧ r = youngEigenvalue YL YR Y} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
