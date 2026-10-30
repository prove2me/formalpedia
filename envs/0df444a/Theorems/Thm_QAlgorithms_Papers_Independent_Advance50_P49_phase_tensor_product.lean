-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_tensor_product
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_tensor_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:11:37.400131+00:00
-- url     : https://prove2.me/theorems/894a57ef-0c13-408e-8cfb-bf29480d94aa
-- title:
--   Proposition 3: tensor-product law for l-body phases
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $V_A,V_B$ be invariant unitaries on $n_A,n_B$ qubits. For every even $l\ge0$,
--   $$\Phi_l(V_A\otimes V_B)=2^{n_B}\Phi_l(V_A)+2^{n_A}\Phi_l(V_B)\pmod{2\pi}.$$
--   Each phase is extended by zero beyond the physical range of its own register. In particular tensoring with a one-qubit identity doubles the phase. This transports phase constraints under ancillary identity factors without dividing modular angles.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 25, Proposition 3: tensor-product law for l-body phases

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

/-- PDF pp.25–26, Proposition 3/G13: each factor is multiplied by the dimension
of the other subsystem. No division of modular phases is performed. -/
theorem phase_tensor_product (nA nB l : ℕ) (hl : Even l)
    (VA : Op nA) (VB : Op nB) (hA : SymUnitary VA) (hB : SymUnitary VB) :
    bodyPhase (registerTensor VA VB) l =
      (2^nB : ℕ) • bodyPhase VA l + (2^nA : ℕ) • bodyPhase VB l := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
