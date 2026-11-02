-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_selfInverse_oneQubit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.selfInverse_oneQubit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:47:59.230556+00:00
-- url     : https://prove2.me/theorems/bc044a71-e59e-4629-9c2a-91ac1a8ab31c
-- title:
--   Self-inverse one-qubit unitaries
-- statement:
--   Let $U$ be a two-dimensional unitary matrix satisfying $U^2=I$. If $U\in SU(2)$, then
--
--   $$U=I\quad\text{or}\quad U=-I.$$
--
--   If $U\in U(2)\setminus SU(2)$, then
--
--   $$\det U=-1,\qquad U=V\sigma_xV^\dagger\quad\text{for some }V\in SU(2),\qquad\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$
--
--   These are the two cases used to transfer controlled-NOT realizations to controlled involutions. The proof's symbol $SU(N)$ for the conjugator is read as $SU(2)$, consistent with its displayed two-by-two matrix.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 16, Lemma 1: self-inverse one-qubit unitaries

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.16, Lemma 1: both self-inverse one-qubit cases. The special
unitary conjugator has dimension two (the proof's SU(N) is a typo). -/
theorem selfInverse_oneQubit :
    (∀ U : Matrix Bool Bool ℂ, U ∈ Matrix.specialUnitaryGroup Bool ℂ →
      U ^ 2 = 1 → U = 1 ∨ U = -1) ∧
    (∀ U : Matrix Bool Bool ℂ, U ∈ Matrix.unitaryGroup Bool ℂ →
      U ∉ Matrix.specialUnitaryGroup Bool ℂ → U ^ 2 = 1 →
      Matrix.det U = -1 ∧ ∃ V : Matrix Bool Bool ℂ,
        V ∈ Matrix.specialUnitaryGroup Bool ℂ ∧ U = V * pauliX * star V) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
