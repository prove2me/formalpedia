-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_vectorizationRealification
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.vectorizationRealification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:00:25.259777+00:00
-- url     : https://prove2.me/theorems/d92f973e-ece1-439f-8392-38d24ca733d7
-- title:
--   Column vectorization and the real representation of adjoining
-- statement:
--   Let $n\ge1$ and let $K_1,K_2,M$ be arbitrary complex $2^n\times2^n$ matrices. Stack matrix columns to define $\operatorname{vec}$ and put $v_\mathbb R(M)=(\operatorname{vec}\operatorname{Re}M,\operatorname{vec}\operatorname{Im}M)$. If $B=K_2^T\otimes K_1$, then
--
--   $$\operatorname{vec}(K_1MK_2)=B\operatorname{vec}M,\qquad v_\mathbb R(K_1MK_2)=\begin{pmatrix}\operatorname{Re}B&-\operatorname{Im}B\\\operatorname{Im}B&\operatorname{Re}B\end{pmatrix}v_\mathbb R(M).$$
--
--   Writing $T$ for the transpose permutation on stacked coordinates gives
--
--   $$v_\mathbb R(M^\dagger)=\operatorname{diag}(T,-T)v_\mathbb R(M).$$
--
--   No complex matrix acts on every $\operatorname{vec}M$ to produce $\operatorname{vec}(M^\dagger)$. Thus adjoining has the stated real representation, and is not a complex-linear universal inverter. Locality and unitarity are unnecessary for these algebraic identities.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 13, (70)–(75): vectorization and real representation of adjoining

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (70)–(75), PDF pp.13–14: column stacking, real blocks, and the real
adjoining operator. Arbitrary complex matrices are allowed in these identities.
Adjoining has no complex-linear matrix representation, even though its real
representation is explicit; no universal physical inverter is claimed. -/
theorem vectorizationRealification {n : ℕ} (hn : 0 < n) :
    (∀ K1 K2 M : Op (QAlgorithms.Qubits n),
      Matrix.vec (K1 * M * K2) =
        (Matrix.kronecker K2.transpose K1).mulVec (Matrix.vec M)) ∧
    (∀ K1 K2 M : Op (QAlgorithms.Qubits n),
      realVec (K1 * M * K2) =
        (realRepresentation (Matrix.kronecker K2.transpose K1)).mulVec (realVec M)) ∧
    (∀ M : Op (QAlgorithms.Qubits n), realVec M.conjTranspose = adjoiningReal.mulVec (realVec M)) ∧
    (¬ ∃ B : Matrix (QAlgorithms.Qubits n × QAlgorithms.Qubits n)
      (QAlgorithms.Qubits n × QAlgorithms.Qubits n) ℂ,
      ∀ M : Op (QAlgorithms.Qubits n), B.mulVec (Matrix.vec M) = Matrix.vec M.conjTranspose) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
