-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_theorem30
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.theorem30
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:11:19.471481+00:00
-- url     : https://prove2.me/theorems/b8397e05-f53e-4ed7-a001-ed35688d9671
-- title:
--   Explicit unitary reduction of the induced representation
-- statement:
--   Let $k\ge0$. Fix coherent unitary partially reduced irreducible representations (PRIRs) of $S(k+1)$, with real transposition matrices, indexed by every partition of $k+1$. Their restrictions to the subgroup $S(k)$ fixing the last letter use the same chosen lower-irrep matrices in every identically labelled block. Write $d_\eta$ for the actual complex Specht dimension of shape $\eta$, $\varphi^\alpha$ for a lower irrep, and $\psi^\nu$ for an upper irrep. Put $t_a=(a,k+1)$, with $t_{k+1}=1$. All addable shapes are included, with no height truncation. Fix $\alpha\vdash k$. Rows of $Z_\alpha$ are $(a,i)$ with $1\le a\le k+1$, $1\le i\le d_\alpha$; columns are $(\nu,j)$ over every $\nu\supset\alpha$ and all its $d_\nu$ PRIR coordinates. Define $Z_{(a,i),(\nu,j)}=\sqrt{d_\nu}/(\sqrt{k+1}\sqrt{d_\alpha})\,\psi^\nu(t_a)_{(\alpha,i),j}$. Let $\Phi_\alpha$ be the concrete induced coset action and $\Psi_\alpha(\sigma)=\bigoplus_{\nu\supset\alpha}\psi^\nu(\sigma)$. Then
--
--   $$
--   Z_\alpha^*Z_\alpha=I,\qquad Z_\alpha Z_\alpha^*=I,\qquad Z_\alpha^*\Phi_\alpha(\sigma)Z_\alpha=\Psi_\alpha(\sigma)\quad(\sigma\in S(k+1)).
--   $$
--
--   This is the complete explicit construction, both unitary identities and simultaneous intertwining (55)–(58); no runtime claim is added.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 13, Theorem 30

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF p.13, Theorem 30, Eqs.(55)–(58): the defined Z is unitary on both
sides and simultaneously reduces every induced-action matrix. -/
theorem theorem30 {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) :
    (explicitZR R alpha)ᴴ * explicitZR R alpha = 1 ∧
    explicitZR R alpha * (explicitZR R alpha)ᴴ = 1 ∧
    ∀ sigma : Equiv.Perm (Fin (k + 1)),
      (explicitZR R alpha)ᴴ * inducedAction R alpha sigma * explicitZR R alpha =
        prirDirectSumAction R alpha sigma := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
