-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_locality_lie_center
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.locality_lie_center
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:02:27.618988+00:00
-- url     : https://prove2.me/theorems/8c176e60-9d2e-41f2-8c77-fa908f107787
-- title:
--   Proposition 1: center of the locality-generated Lie algebra
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For $0\le k\le n$, including $k=0,1$, the center of the real generated Lie algebra is
--   $$Z(\mathfrak v_k)=\operatorname{span}_{\mathbb R}\{iC_l:0\le l\le2\lfloor k/2\rfloor\}.$$
--   A zero-supported operator is scalar, so the zero-local algebra contains $iI$. This distinguishes the local-gate group from the exchange-only group.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 17, Proposition 1: center of the locality-generated Lie algebra

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

/-- PDF p.17, Proposition 1. Includes k=0 and k=1, with global scalar phases. -/
theorem locality_lie_center (n k : ℕ) (hk : k ≤ n) :
    {A : Op n | A ∈ localLie n k ∧
      ∀ B : Op n, B ∈ localLie n k → A*B=B*A} =
      (centralSpace n k : Set (Op n)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
