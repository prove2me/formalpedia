-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_negative_volume
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.negative_volume
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:07:59.818135+00:00
-- url     : https://prove2.me/theorems/6cbc7343-657e-4933-9906-fa81d980198c
-- title:
--   Lemma 5.1
-- statement:
--   Let $m\ge0$, choose an ordered orthonormal basis of $\mathbb R^{0,m}$, and put $\omega=e_1\cdots e_m$ in the Clifford algebra with $e_i^2=1$. For every vector $x$,
--   $$\begin{cases}\omega x+x\omega=0,&m\text{ even},\\\omega x=x\omega,&m\text{ odd},\end{cases}\qquad\omega^2=\begin{cases}1,&m\equiv0,1\pmod4,\\-1,&m\equiv2,3\pmod4.\end{cases}$$
--   The empty product at $m=0$ is one. The negative-signature square convention is distinct from the positive-signature convention.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 31, Lemma 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 5.1, PDF p. 31: negative-signature volume; square is positive in residues 0,1. -/
theorem negative_volume (m : ℕ)
    (e : Module.Basis (Fin (0 + m)) ℝ ((Fin (0 + m) → ℝ))) (he : PseudoOrthonormal 0 m e) :
    (∀ x : (Fin (0 + m) → ℝ),
      if Even m then volumeElement 0 m e * CliffordAlgebra.ι (cliffordQ (signatureMatrix 0 m)) x +
        CliffordAlgebra.ι (cliffordQ (signatureMatrix 0 m)) x * volumeElement 0 m e = 0
      else volumeElement 0 m e * CliffordAlgebra.ι (cliffordQ (signatureMatrix 0 m)) x =
        CliffordAlgebra.ι (cliffordQ (signatureMatrix 0 m)) x * volumeElement 0 m e) ∧
    volumeElement 0 m e ^ 2 = if m % 4 = 0 ∨ m % 4 = 1 then 1 else -1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
