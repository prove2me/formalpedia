-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_proposition_2_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.proposition_2_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:28:44.220623+00:00
-- url     : https://prove2.me/theorems/9dedb157-9839-4b89-9008-df4cf5d9a0be
-- title:
--   Proposition 2.4: independent input/output permutation symmetry
-- statement:
--   Let $d\ge2$ and let $\Phi$ be a CPTP $p\to q$ qudit channel, with unnormalized input-first Choi operator $X^\Phi$. Let $P_\pi|x\rangle=|x\circ\pi^{-1}\rangle$. The channel is invariant under permutations of its inputs and independently invariant under permutations of its outputs if and only if
--   $$
--   [X^\Phi,P_\pi\otimes P_\sigma]=0
--   \qquad\text{for every }(\pi,\sigma)\in S_p\times S_q.
--   $$
--   Both channel invariances are required on every density matrix. This characterizes the additional permutation symmetry used in the applications.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 12, Proposition 2.4: independent input/output permutation symmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.12, Proposition 2.4: the input and output permutations are independent. -/
theorem proposition_2_4 {d p q : ℕ} (hd : 2 ≤ d)
    (Phi : Superop (Sites (Fin d) p) (Sites (Fin d) q)) (hPhi : IsChannel Phi) :
    SymmetricChannel Phi ↔
      ∀ (pi : Equiv.Perm (Fin p)) (sigma : Equiv.Perm (Fin q)),
        Commute (choi Phi)
          (Matrix.kronecker ((QAlgorithms.Schur.tensorPermutation _ _) pi) ((QAlgorithms.Schur.tensorPermutation _ _) sigma)) := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
