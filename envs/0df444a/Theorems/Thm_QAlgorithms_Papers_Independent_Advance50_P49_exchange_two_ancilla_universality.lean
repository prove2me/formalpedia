-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_exchange_two_ancilla_universality
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.exchange_two_ancilla_universality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:57:03.722983+00:00
-- url     : https://prove2.me/theorems/995ea73c-74b9-4c9c-a0d1-5b2cd0c1aeb6
-- title:
--   Main result: exchange universality with two ancillary qubits
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For every invariant unitary $V$ on $\mathcal H_n$, there are a finite exchange circuit $W$ on the chain of $n+2$ qubits and a real $\alpha$, both chosen independently of the input, such that for every normalized $\psi\in\mathcal H_n$,
--   $$W(\psi\otimes|00\rangle)=e^{i\alpha}(V\psi)\otimes|00\rangle.$$
--   Thus two ancillas suffice for full physical-register universality and are returned unchanged. No efficiency or gate-count bound is asserted.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 1, Main result: exchange universality with two ancillary qubits

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

/-- PDF p.1, pinned to pp.31–33, I24: universality on the full physical register
with two returned ancillas and an explicit allowed global phase. -/
theorem exchange_two_ancilla_universality (n : ℕ) (V : Op n) (hV : SymUnitary V) :
    ∃ (W : Op (n+2)) (alpha : ℝ), W ∈ exchangeGroup (n+2) true false ∧
      ∀ psi : Vec n, IsState psi →
        act W (tensorState psi (zeroKet 2)) =
          Complex.exp (Complex.I * alpha) • tensorState (act V psi) (zeroKet 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
