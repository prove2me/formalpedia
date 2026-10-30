-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_lemma26
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.lemma26
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:08:45.588987+00:00
-- url     : https://prove2.me/theorems/802c6a4a-cfdd-48e2-9887-24df73e40fff
-- title:
--   Weighted diagonal PRIR transposition sum
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. Fix a lower shape $\alpha$, internal indices $i,j$, and $b\in\{1,\ldots,k+1\}$. Sum over every addable upper shape $\nu\supset\alpha$. Then
--
--   $$
--   \sum_{\nu\supset\alpha}d_\nu\psi^{\nu;\alpha\alpha}_{ij}(t_b)=(k+1)d_\alpha\delta_{b,k+1}\delta_{ij}.
--   $$
--
--   The sum is over the complete induced representation, including branches absent from the physical height-truncated representation.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 10, Lemma 26

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF p.10, Lemma 26, Eq.(33), with n=k+2. -/
theorem lemma26 {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k)
    (b : Fin (k + 1)) (i j : Fin (irrepDim alpha)) :
    weightedBlock R alpha (cosetRep b) i j =
      if b = Fin.last k ∧ i = j then ((k + 1 : ℕ) : ℂ) * (irrepDim alpha : ℂ) else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
