-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary31
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary31
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:12:02.752416+00:00
-- url     : https://prove2.me/theorems/ffd1e590-d4ba-4828-b59c-47f4a4fef5c1
-- title:
--   Explicit columns form a complete orthonormal basis
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. Fix $\alpha\vdash k$ and let $Z_\alpha$ be the explicit matrix of (55). For each column label $(\nu,j)$, let $T_{\nu,j}$ be that column as a vector in $\mathbb C^{(k+1)d_\alpha}$. Then
--
--   $$
--   \#\{(\nu,j)\}=(k+1)d_\alpha,\qquad \{T_{\nu,j}\}_{\nu\supset\alpha,\,1\le j\le d_\nu}\text{ is an orthonormal basis of }\mathbb C^{(k+1)d_\alpha}.
--   $$
--
--   Completeness is asserted through an actual orthonormal basis equal to the specified columns.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 14, Corollary 31

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF p.14, Corollary 31: all explicitly defined columns form an
orthonormal basis, with the asserted total number of columns. -/
theorem corollary31 {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) :
    Fintype.card (ZColumn alpha) = (k + 1) * irrepDim alpha ∧
    ∃ b : OrthonormalBasis (ZColumn alpha) ℂ
      (EuclideanSpace ℂ (Fin (k + 1) × Fin (irrepDim alpha))),
      ∀ q, b q = columnT R alpha q := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
