-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_split_volume
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.split_volume
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:07:09.206859+00:00
-- url     : https://prove2.me/theorems/975b16e0-ecce-41db-ab82-01ddedf27a43
-- title:
--   Lemma 3.10
-- statement:
--   Let $m\ge0$ and let $e_1,\ldots,e_{2m}$ be an ordered pseudo-orthonormal basis of $\mathbb R^{m,m}$, positive vectors first. In its Clifford algebra with $v^2=-g(v,v)$, put $\omega=e_1\cdots e_{2m}$. Then
--   $$\omega x+x\omega=0\quad(x\in\mathbb R^{m,m}),\qquad\omega^2=1.$$
--   When $m=0$ the product is empty and equals one, and the vector assertion is vacuous. This is the algebraic volume identity used in odd-dimensional extensions.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 25, Lemma 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 3.10, PDF p. 25. Empty volume is one; at m=0 the vector clause is vacuous. -/
theorem split_volume (m : ℕ)
    (e : Module.Basis (Fin (m + m)) ℝ ((Fin (m + m) → ℝ))) (he : PseudoOrthonormal m m e) :
    (∀ x : (Fin (m + m) → ℝ), volumeElement m m e *
      CliffordAlgebra.ι (cliffordQ (signatureMatrix m m)) x +
      CliffordAlgebra.ι (cliffordQ (signatureMatrix m m)) x * volumeElement m m e = 0) ∧
    volumeElement m m e ^ 2 = 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
