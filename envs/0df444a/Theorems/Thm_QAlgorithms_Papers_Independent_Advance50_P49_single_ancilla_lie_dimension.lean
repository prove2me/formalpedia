-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_single_ancilla_lie_dimension
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.single_ancilla_lie_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:21:58.269913+00:00
-- url     : https://prove2.me/theorems/ddc5d8eb-7e42-4f41-b9be-d3cae7bca181
-- title:
--   One-ancilla assistance does not enlarge the realizable Lie-algebra dimension
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For $2\le k\le n$, consider the assisted tangent space $\mathfrak a_k=\{A:A\otimes I_2\in\mathfrak v_k(n+1)\}$. Then
--   $$\mathfrak a_k=\mathfrak v_k(n),\qquad \dim_{\mathbb R}\mathfrak a_k=\dim_{\mathbb R}\mathfrak v_k(n).$$
--   The real span used to bundle the preimage is the same subspace. This identifies the associated Lie algebra of invariant targets whose tensor-identity endpoint is reachable with one ancilla; it does not assert equality of reachable groups or eliminate finite disconnected components.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 36, One-ancilla assistance does not enlarge the realizable Lie-algebra dimension

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

/-- PDF p.36: equality of tangent algebras and real dimensions under one-ancilla
assistance. No equality of reachable groups is asserted. -/
theorem single_ancilla_lie_dimension (n k : ℕ) (hlo : 2 ≤ k) (hhi : k ≤ n) :
    assistedLieSet n k = (localLie n k : Set (Op n)) ∧
    assistedLie n k = (localLie n k).toSubmodule ∧
    Module.finrank ℝ (assistedLie n k) = Module.finrank ℝ (localLie n k) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
