-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_jointZQuantumOrders
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.jointZQuantumOrders
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:51:58.715739+00:00
-- url     : https://prove2.me/theorems/61183369-c37d-4eb8-a0b7-b6118408ef68
-- title:
--   Joint z-rotations and odd quantum orders
-- statement:
--   Let $n\ge1$ and $F_z=\frac12\sum_\ell Z_\ell$. An operator $T$ has integer quantum order $p$ when $[F_z,T]=pT$. For $K_z(\phi)=\bigotimes_\ell e^{-i\phi Z_\ell/2}$,
--
--   $$K_z(\phi)T K_z(\phi)^\dagger=e^{-ip\phi}T.$$
--
--   If $T\ne0$, this equals $-T$ exactly when $p\phi=(2z+1)\pi$ for some integer $z$. For every positive integer $r$, the angle $\phi=\pi/r$ therefore simultaneously reverses every finite complex linear combination of operators having orders $p=\pm r(2q+1)$ with $q\ge0$. This includes the first entry $p=\pm r$ of Table III, and allows the linear combination itself to vanish. No physical realization of every possible tensor rank is asserted.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 7, (33)–(35), Table III: joint z rotations and quantum orders

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (33)–(35) and Table III, PDF p.7. The commutator quantum-order
interface also applies to non-Hermitian tensors. Printed: q=1,2,... after
the table. Changed: q starts at 0. Why: the table explicitly starts with
p=r, and the phase condition gives every odd multiple r(2q+1). -/
theorem jointZQuantumOrders {n : ℕ} (hn : 0 < n) :
    (∀ (T : Op (QAlgorithms.Qubits n)) (p : ℤ), HasOrder T p → ∀ phi : ℝ,
      adjointConjugation (jointZ n phi) T = Complex.exp (-Complex.I * (p : ℂ) * (phi : ℂ)) • T) ∧
    (∀ (T : Op (QAlgorithms.Qubits n)) (p : ℤ), HasOrder T p → T ≠ 0 → ∀ phi : ℝ,
      (adjointConjugation (jointZ n phi) T = -T ↔ OddPi ((p : ℝ) * phi))) ∧
    (∀ (r : ℕ), 0 < r → ∀ (m : ℕ) (T : Fin m → Op (QAlgorithms.Qubits n))
      (p : Fin m → ℤ) (c : Fin m → ℂ),
      (∀ a, HasOrder (T a) (p a)) →
      (∀ a, ∃ q : ℕ, p a = (r : ℤ) * (2 * (q : ℤ) + 1) ∨
        p a = -(r : ℤ) * (2 * (q : ℤ) + 1)) →
      adjointConjugation (jointZ n (Real.pi / r)) (∑ a, c a • T a) = -(∑ a, c a • T a)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
