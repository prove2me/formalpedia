-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_two_local_counterexample
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.two_local_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:37:57.604988+00:00
-- url     : https://prove2.me/theorems/a8794041-ddaa-42da-a585-52e4eb7406ac
-- title:
--   Unnumbered two-local symmetry counterexample in the discussion
-- statement:
--   Consider the explicit four-qubit, two-logical-qubit encoding $$|a,b\rangle\mapsto\frac{|0,b,a,a\oplus b\rangle+|1,\neg b,\neg a,\neg(a\oplus b)\rangle}{\sqrt2}.$$ It is isometric and corrects erasure of each one of its four physical qubits. The Hermitian operator $Q=X\otimes X\otimes I\otimes I$ implements the nontrivial first-logical-qubit Pauli $X_L$, so $$QV=VX_L,\qquad e^{-i\theta Q}V=Ve^{-i\theta X_L}\quad(\theta\in\mathbb R).$$ This explains why a two-site charge need not obstruct correction of only single-site erasures.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 23, Unnumbered two-local symmetry counterexample in the discussion

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.23: the explicit two-local continuous symmetry coexists with exact single erasure
correction. This is not a counterexample to Theorem 2's compatible-support hypothesis. -/
theorem two_local_counterexample :
    twoLocalEncodingᴴ * twoLocalEncoding = 1 ∧
    (∀ i : Fin 4, CorrectsUniformErasure twoLocalEncoding (fun _ => false) {i}) ∧
    twoLocalQ.IsHermitian ∧ firstLogicalX ≠ 1 ∧
    twoLocalQ * twoLocalEncoding = twoLocalEncoding * firstLogicalX ∧
    ∀ theta : ℝ, chargeEvolution twoLocalQ theta * twoLocalEncoding =
      twoLocalEncoding * chargeEvolution firstLogicalX theta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
