-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_central_partial_trace
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.central_partial_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:00:43.375992+00:00
-- url     : https://prove2.me/theorems/a340d575-1365-488a-8073-8ec405e83fd8
-- title:
--   Remark 1 and Eq.(B7): partial traces of C_l
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Partition $n=n_A+n_B$ wires into the first $n_A$ and last $n_B$ wires. For every even $l\ge0$,
--   $$\operatorname{Tr}_A C_l^{(n)}=2^{n_A}C_l^{(n_B)},\qquad \operatorname{Tr}_B C_l^{(n)}=2^{n_B}C_l^{(n_A)}.$$
--   The zero extension above the physical range is part of the statement. In particular $l=0$ produces dimension factors rather than zero. These formulas transport the central observables between tensor factors.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 10, Remark 1 and Eq.(B7): partial traces of C_l

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

/-- PDF p.10, Remark 1 and B7: partial trace over either factor, including l=0
and indices exceeding one or both subsystem sizes. -/
theorem central_partial_trace (nA nB l : ℕ) (hl : Even l) :
    (2 * ((nA+nB)/2) < l → central (nA+nB) l = 0) ∧
    traceLeft (registerSplit (n := nA) (m := nB) (central (nA+nB) l)) =
      (2 : ℂ)^nA • central nB l ∧
    QAlgorithms.traceRight (registerSplit (n := nA) (m := nB) (central (nA+nB) l)) =
      (2 : ℂ)^nB • central nA l := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
