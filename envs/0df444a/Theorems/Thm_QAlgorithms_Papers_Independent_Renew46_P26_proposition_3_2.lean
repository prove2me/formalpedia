-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_proposition_3_2
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.proposition_3_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:52:34.354783+00:00
-- url     : https://prove2.me/theorems/6af4771f-b0bf-402d-bf4a-fdc09b4ea4ab
-- title:
--   Proposition 3.2
-- statement:
--   For $n\geq2$, let $H(2)$ be the complex algebra presented by $s^2=1$, $Y_1Y_2=Y_2Y_1$, and $sY_1+1=Y_2s$. There is a unital algebra map $f:H(2)\to\mathbb C[S_n]$ with
--
--   $$f(Y_1)=X_{n-1},\qquad f(Y_2)=X_n,\qquad f(s)=(n-1,n),\qquad \mathbb C[S_n]=\langle\mathbb C[S_{n-1}],f(H(2))\rangle.$$
--
--   Only the image of the presented algebra is used; no embedding of the infinite-dimensional $H(2)$ is asserted.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 15, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 3.2 (PDF p.15). H(2) maps to the algebra by its specified
YJM/Coxeter generators; only its image is used. The explicit swapAlgebraElement
(n+1,n+2) resolves the source's shifted subscript s_n. -/
theorem proposition_3_2 (n : ℕ) :
    ∃ f : Hecke 2 →ₐ[ℂ] SymmetricAlgebra (n + 2),
      f (heckeY (0 : Fin 2)) = yjm ⟨n, by omega⟩ ∧
      f (heckeY (1 : Fin 2)) = yjm ⟨n + 1, by omega⟩ ∧
      f (heckeS (⟨0, by decide⟩ : Adjacent 2)) =
        swapAlgebraElement (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩ ∧
      Algebra.adjoin ℂ ((prefixAlgebra (by omega : n + 1 ≤ n + 2) :
        Set (SymmetricAlgebra (n + 2))) ∪ (f.range : Set (SymmetricAlgebra (n + 2)))) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
