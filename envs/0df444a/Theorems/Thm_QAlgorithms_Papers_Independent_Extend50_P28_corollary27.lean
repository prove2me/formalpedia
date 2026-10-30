-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary27
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary27
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:09:30.694107+00:00
-- url     : https://prove2.me/theorems/ef8d054d-d5f1-48ed-8ed8-7eb4bcfca477
-- title:
--   Weighted PRIR block sums on and off the subgroup
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. For a fixed lower shape $\alpha$, put $B_\alpha(\sigma)=\sum_{\nu\supset\alpha}d_\nu\psi^{\nu;\alpha\alpha}(\sigma)$. If $\gamma\in S(k)$ and $b\in\{1,\ldots,k+1\}$, then
--
--   $$
--   B_\alpha(\gamma t_b)=(k+1)d_\alpha\delta_{b,k+1}\varphi^\alpha(\gamma),\qquad B_\alpha(\sigma)=0\ (\sigma\notin S(k)),\qquad B_\alpha(\gamma)=(k+1)d_\alpha\varphi^\alpha(\gamma).
--   $$
--
--   All three source clauses are retained; subgroup evaluation uses the actual fixing-last-letter embedding.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 11, Corollary 27

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF pp.11–12, Corollary 27: all three clauses (43)–(45). -/
theorem corollary27 {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) :
    (∀ (gamma : Equiv.Perm (Fin k)) (b : Fin (k + 1)) (i j : Fin (irrepDim alpha)),
      weightedBlock R alpha (extendPerm gamma * cosetRep b) i j =
        if b = Fin.last k then
          ((k + 1 : ℕ) : ℂ) * (irrepDim alpha : ℂ) * R.lower alpha gamma i j else 0) ∧
    (∀ (sigma : Equiv.Perm (Fin (k + 1))) (i j : Fin (irrepDim alpha)),
      (¬ ∃ gamma, extendPerm gamma = sigma) → weightedBlock R alpha sigma i j = 0) ∧
    (∀ (gamma : Equiv.Perm (Fin k)) (i j : Fin (irrepDim alpha)),
      weightedBlock R alpha (extendPerm gamma) i j =
        ((k + 1 : ℕ) : ℂ) * (irrepDim alpha : ℂ) * R.lower alpha gamma i j) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
