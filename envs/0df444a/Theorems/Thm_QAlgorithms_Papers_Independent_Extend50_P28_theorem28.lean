-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_theorem28
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.theorem28
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:10:37.587347+00:00
-- url     : https://prove2.me/theorems/f3a6b448-a513-40a2-90f2-b027ec66edf2
-- title:
--   Induced-action weighted PRIR summation rule
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. Let $\alpha$ be a lower shape and define $B_\alpha$ as the weighted diagonal-block sum. For every $\sigma\in S(k+1)$ and $a,b\in\{1,\ldots,k+1\}$,
--
--   $$
--   B_\alpha(t_a\sigma t_b)=\begin{cases}(k+1)d_\alpha\varphi^\alpha(t_a\sigma t_b),&a=\sigma(b),\\0,&a\ne\sigma(b),\end{cases}\qquad B_\alpha(t_at_b)=(k+1)d_\alpha\delta_{ab}I_{d_\alpha}.
--   $$
--
--   The conditional branch ensures the lower representation is evaluated only on a subgroup element. Both (47) and (48) are stated.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 12, Theorem 28

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF p.12, Theorem 28: the conditional subgroup expression (47) and
its identity-permutation specialization (48). -/
theorem theorem28 {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) :
    (∀ (sigma : Equiv.Perm (Fin (k + 1))) (a b : Fin (k + 1))
      (i j : Fin (irrepDim alpha)),
      weightedBlock R alpha (cosetRep a * sigma * cosetRep b) i j =
        if a = sigma b then ((k + 1 : ℕ) : ℂ) * (irrepDim alpha : ℂ) *
          R.lower alpha (lowerPerm (cosetRep a * sigma * cosetRep b)) i j else 0) ∧
    (∀ (a b : Fin (k + 1)) (i j : Fin (irrepDim alpha)),
      weightedBlock R alpha (cosetRep a * cosetRep b) i j =
        if a = b ∧ i = j then ((k + 1 : ℕ) : ℂ) * (irrepDim alpha : ℂ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
