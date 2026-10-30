-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_locality
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_locality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:12:23.064583+00:00
-- url     : https://prove2.me/theorems/dc18f86e-0101-445d-8e9f-f4944f3bab93
-- title:
--   Necessary phase constraints for k-local realizability
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   If $V\in\mathcal V_k$ for a natural locality bound $k$, then for every even $l>k$,
--   $$\Phi_l(V)=0\pmod{2\pi}.$$
--   The zero extension covers $l$ above the physical range. Hence a nonzero such phase certifies nonmembership in $\mathcal V_k$. This is a necessary condition on a single endpoint, with no converse asserted here.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 26, Necessary phase constraints for k-local realizability

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

/-- PDF pp.4,26: an exact necessary condition at a fixed unitary endpoint. -/
theorem phase_locality (n k : ℕ) (V : Op n) (hV : V ∈ localGroup n k) :
    ∀ l : ℕ, Even l → k<l → bodyPhase V l=0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
