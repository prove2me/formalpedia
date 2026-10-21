-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_remark_3_3
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.remark_3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:53:08.559167+00:00
-- url     : https://prove2.me/theorems/9058678c-fc0e-4cbe-ac3d-c2d12a4b53c7
-- title:
--   Remark 3.3
-- statement:
--   Let $H(n)$ be generated over $\mathbb C$ by commuting $Y_1,\ldots,Y_n$ and Coxeter involutions $s_1,\ldots,s_{n-1}$, subject to distant commutation and $s_iY_i+1=Y_{i+1}s_i$. Then
--
--   $$H(n)/(Y_1)\ \cong\ \mathbb C[S_n],\qquad Y_i\longmapsto X_i,\quad s_i\longmapsto(i,i+1).$$
--
--   The isomorphism is pinned on every generator. At $n=0$, the presentation has no generators and the quotient imposes no additional relation.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 15, Remark 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Remark 3.3 (PDF p.15). The quotient H(n)/(Y_1) is canonically C[S_n],
with the images of every generator pinned. n=0 gives the scalar algebra. -/
theorem remark_3_3 (n : ℕ) :
    ∃ e : RingQuot (KillFirst n) ≃ₐ[ℂ] SymmetricAlgebra n,
      (∀ i : Fin n, e (RingQuot.mkAlgHom ℂ (KillFirst n) (heckeY i)) = yjm i) ∧
      (∀ i : Adjacent n,
        e (RingQuot.mkAlgHom ℂ (KillFirst n) (heckeS i)) = adjacentElement i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
