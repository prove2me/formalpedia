-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_proposition25
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.proposition25
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:08:18.990966+00:00
-- url     : https://prove2.me/theorems/f8f9e643-525f-419f-bb5a-7b235cbb63b3
-- title:
--   Bilinear orthogonality of coherent PRIR blocks
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. Suppose $\alpha,\beta\subset\mu$ and $\beta,\gamma\subset\nu$ are removable shapes, and $i,j$ are internal indices in $\alpha,\gamma$. Then
--
--   $$
--   \sum_{a=1}^{k+1}\sum_{r=1}^{d_\beta}\psi^{\mu;\alpha\beta}_{ir}(t_a)\psi^{\nu;\beta\gamma}_{rj}(t_a)=\frac{(k+1)d_\beta}{d_\mu}\delta_{\mu\nu}\delta_{\alpha\gamma}\delta_{ij}.
--   $$
--
--   This supplies the source bilinear summation identity in compatible lower coordinates.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 10, Proposition 25

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF p.10, Proposition 25, Eq.(32), with n=k+1. Both common beta blocks
use the same lower representation through CoherentPRIR.restriction. -/
theorem proposition25 {k : ℕ} (R : CoherentPRIR k)
    (mu nu : Shape (k + 1)) (alpha beta gamma : Shape k)
    (ham : oneBoxBranch alpha mu) (hbm : oneBoxBranch beta mu)
    (hbn : oneBoxBranch beta nu) (hgn : oneBoxBranch gamma nu)
    (i : Fin (irrepDim alpha)) (j : Fin (irrepDim gamma)) :
    (∑ a : Fin (k + 1), ∑ r : Fin (irrepDim beta),
      prirBlock R mu alpha beta ham hbm (cosetRep a) i r *
      prirBlock R nu beta gamma hbn hgn (cosetRep a) r j) =
    if mu = nu ∧ alpha = gamma ∧ i.val = j.val then
      ((k + 1 : ℕ) : ℂ) * (irrepDim beta : ℂ) / (irrepDim mu : ℂ) else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
