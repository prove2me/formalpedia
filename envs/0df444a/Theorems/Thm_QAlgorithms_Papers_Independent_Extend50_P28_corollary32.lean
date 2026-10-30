-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary32
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary32
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:12:40.923994+00:00
-- url     : https://prove2.me/theorems/0089911f-a423-4d09-a551-29ea43b99ae7
-- title:
--   Explicit diagonalization and eigenvectors of the Gram matrix
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. Let $d$ be a natural number and $\alpha\vdash k$. Let $Q_\alpha$ be Definition 7: its diagonal coset blocks are $dI$, and its off-diagonal $(a,b)$ block is $\varphi^\alpha(t_a(a,b)t_b)$. For a one-box branch $\nu$, let $c(\nu/\alpha)$ be the added box column minus row, and set $\lambda_\nu(\alpha)=d+c(\nu/\alpha)$. With the explicit $Z_\alpha$ and columns $T_{\nu,j}$,
--
--   $$
--   Z_\alpha^*Q_\alpha Z_\alpha=\operatorname{diag}_{\nu,j}(\lambda_\nu(\alpha)),\qquad Q_\alpha T_{\nu,j}=\lambda_\nu(\alpha)T_{\nu,j}.
--   $$
--
--   Each branch eigenvalue occurs in its entire irrep block, including zero branches; no positivity claim for nonphysical lower shapes is inserted.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 14, Corollary 32

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF p.14, Corollary 32, Eq.(60): full Gram diagonalization and the
explicit eigenvectors. No positive-support truncation and no PSD hypothesis. -/
theorem corollary32 {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) (d : ℕ) :
    (explicitZR R alpha)ᴴ * gramQ R alpha d * explicitZR R alpha = contentDiagonal alpha d ∧
    ∀ q : ZColumn alpha,
      QAlgorithms.act (gramQ R alpha d) (columnT R alpha q) =
        (contentEigenvalue d alpha.val q.1.val.val : ℂ) • columnT R alpha q := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
