-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_single_ancilla_factorization
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.single_ancilla_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:20:30.99442+00:00
-- url     : https://prove2.me/theorems/543c6e55-7557-4dc7-8fe0-c6df824fbc36
-- title:
--   Single-ancilla exact implementation forces a tensor identity
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $V$ on $n$ qubits and $W$ on $n+1$ qubits be invariant unitaries. Let $\eta,\eta'$ be fixed normalized one-qubit vectors. If $W(\psi\otimes\eta)=(V\psi)\otimes\eta'$ for every normalized data vector $\psi$, then
--   $$\exists\alpha\in\mathbb R:\quad \eta'=e^{i\alpha}\eta,\qquad W=e^{i\alpha}(V\otimes I).$$
--   In particular, if $\eta'=\eta$ then $W=V\otimes I$. This is an endpoint factorization and says nothing about whether an implementation circuit interacted with the ancilla at intermediate times.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 36, Single-ancilla exact implementation forces a tensor identity

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

/-- PDF p.36, J1–J8: arbitrary fixed normalized ancillary input/output.
The conclusion concerns the endpoint, not the intermediate interaction circuit. -/
theorem single_ancilla_factorization (n : ℕ) (V : Op n) (W : Op (n+1))
    (hV : SymUnitary V) (hW : SymUnitary W) (eta etaOut : Vec 1)
    (hEta : IsState eta) (hOut : IsState etaOut)
    (hAct : ∀ psi : Vec n, IsState psi →
      act W (tensorState psi eta) = tensorState (act V psi) etaOut) :
    (∃ alpha : ℝ, etaOut=Complex.exp (Complex.I*alpha) • eta ∧
      W=Complex.exp (Complex.I*alpha) • registerTensor V (1 : Op 1)) ∧
    (etaOut=eta → W=registerTensor V (1 : Op 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
