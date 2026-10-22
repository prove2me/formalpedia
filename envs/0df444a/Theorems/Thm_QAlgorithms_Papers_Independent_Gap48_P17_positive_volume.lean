-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_positive_volume
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.positive_volume
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:07:34.366201+00:00
-- url     : https://prove2.me/theorems/316771d6-6357-4c2d-a796-5bdf6cfaa48b
-- title:
--   Lemma 4.2
-- statement:
--   Let $m\ge0$, choose an ordered orthonormal basis of the positive space $\mathbb R^{m,0}$, and put $\omega=e_1\cdots e_m$ in the Clifford algebra with $e_i^2=-1$. For every vector $x$,
--   $$\begin{cases}\omega x+x\omega=0,&m\text{ even},\\\omega x=x\omega,&m\text{ odd},\end{cases}\qquad\omega^2=\begin{cases}1,&m\equiv0,3\pmod4,\\-1,&m\equiv1,2\pmod4.\end{cases}$$
--   The empty product at $m=0$ is one. Both commutation parity and the square are part of the statement.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 26, Lemma 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 4.2, PDF p. 26: positive-signature volume, both commutation and square formulas. -/
theorem positive_volume (m : ℕ)
    (e : Module.Basis (Fin (m + 0)) ℝ ((Fin (m + 0) → ℝ))) (he : PseudoOrthonormal m 0 e) :
    (∀ x : (Fin (m + 0) → ℝ),
      if Even m then volumeElement m 0 e * CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x +
        CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x * volumeElement m 0 e = 0
      else volumeElement m 0 e * CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x =
        CliffordAlgebra.ι (cliffordQ (signatureMatrix m 0)) x * volumeElement m 0 e) ∧
    volumeElement m 0 e ^ 2 = if m % 4 = 0 ∨ m % 4 = 3 then 1 else -1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
