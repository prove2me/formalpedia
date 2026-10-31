-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_one_qubit_gate_teleportation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.one_qubit_gate_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:32:35.865979+00:00
-- url     : https://prove2.me/theorems/6fd61e4b-3a54-4f9a-b269-a09d0ea6a33e
-- title:
--   §2: one-qubit gate teleportation
-- statement:
--   Let $U$ be any one-qubit unitary, and write $|B_{cd}\rangle=(Z^cX^d\otimes I)|\phi_2\rangle$ for bits $c,d$, where $|\phi_2\rangle=(|00\rangle+|11\rangle)/\sqrt2$. The four kets $|B(U)_{cd}\rangle=(U^\dagger\otimes I)|B_{cd}\rangle$ are orthonormal. For every normalized input $|\psi\rangle$, measuring registers $1,2$ against one of these kets, with resource $|\phi_2\rangle_{23}$, gives
--
--   $$ |b_{cd}\rangle=\frac12 X^dZ^cU|\psi\rangle,\qquad \Pr(c,d)=\|b_{cd}\|^2=\frac14. $$
--
--   Thus $2|b_{cd}\rangle$ is the conditional output. The choice $U=I$ includes ordinary teleportation with the same labels.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 2, §2: one-qubit gate teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Rotated Bell gate teleportation, PDF pp.2–4, including U=I as Fig.1.
All four measured kets are orthonormal; branches retain their coefficient 1/2. -/
theorem one_qubit_gate_teleportation (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    Orthonormal ℂ (fun p : QubitPair => rotatedBell U p.1 p.2) ∧
    ∀ (psi : Vec Bool), IsState psi → ∀ c d : Bool,
      let b := teleportContraction psi (finiteMaxEntangled Bool) (rotatedBell U c d)
      b = (1 / 2 : ℂ) • act (pauliByproduct d c * U) psi ∧
      ‖b‖ ^ 2 = (1 / 4 : ℝ) ∧ (2 : ℂ) • b = act (pauliByproduct d c * U) psi := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
