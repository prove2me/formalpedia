-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_odd_pauli_sector_trace
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.odd_pauli_sector_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:06:27.364482+00:00
-- url     : https://prove2.me/theorems/8d0bf020-f8ea-4b2e-9db4-974fc71504e9
-- title:
--   Proposition 2: odd Pauli weight has vanishing sector trace
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $A$ lie in the complex span of phase-free Pauli strings with an odd number of nonidentity factors. No Hermiticity or rotational invariance is assumed for the trace assertion:
--   $$\operatorname{Tr}(A\Pi_j)=0\quad\text{for every legal }j.$$
--   If $A$ is additionally Hermitian and invariant, then $iA$ belongs to the exchange-generated real Lie algebra and $e^{-itA}$ is a finite exchange circuit for every real $t$. The latter hypotheses belong only to the implementation consequence.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 23, Proposition 2: odd Pauli weight has vanishing sector trace

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P49

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

attribute [local instance 100] LieRing.ofAssociativeRing

-- Specialize the frozen generic aliases without declaring new aliases.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "Vec" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Vec (Qubits n))

-- The frozen support predicate takes the support before the operator.

local notation "WireSupported" => QAlgorithms.Papers.Independent.Information100.P69.Supported

/-- PDF p.23, Proposition 2. The trace claim is for arbitrary operators;
Hermiticity and symmetry apply only to the exchange-realizability consequence. -/
theorem odd_pauli_sector_trace (n : ℕ) (A : Op n) (hA : A ∈ oddPauliSpace n) :
    (∀ j : Spin n, Matrix.trace (A*spinProjector n j)=0) ∧
    (A.IsHermitian → RotationInvariant A → Complex.I • A ∈ exchangeLie n false false ∧
      ∀ t : ℝ, evolve A t ∈ exchangeGroup n false false) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
