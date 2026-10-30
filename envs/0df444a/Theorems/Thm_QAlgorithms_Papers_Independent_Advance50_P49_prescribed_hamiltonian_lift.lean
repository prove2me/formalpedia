-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_prescribed_hamiltonian_lift
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.prescribed_hamiltonian_lift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:17:42.795924+00:00
-- url     : https://prove2.me/theorems/4ef69fdb-bcda-4fbc-b0bf-40fdfa16e746
-- title:
--   Theorem 4: prescribed two-ancilla Hamiltonian lift
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $n\ge1$ and let $H$ be Hermitian and invariant. Set $Q_l=R_{12}\cdots R_{l-1,l}$ and
--   $$\widetilde Q_l=2^{-l/2}\left[2Q_2\otimes I+\sum_{s=4}^{l}2^{s/2}(Q_s\otimes I-Q_{s-2}\otimes R_{ab})\right].$$
--   Let $\mathcal P$ average over permutations of data wires only, $\widetilde E_l=n!\mathcal P(\widetilde Q_l)/((n-l)!(l/2)!)$, and define
--   $$\widetilde H=(H-\operatorname{Tr}(H)I/2^n)\otimes I+\sum_{l=2}^{2\lfloor n/2\rfloor}\frac{\operatorname{Tr}(HC_l)}{\operatorname{Tr}(C_l^2)}(\widetilde E_l-C_l\otimes I).$$
--   Then $\widetilde H$ is Hermitian, $i\widetilde H$ lies in the real Lie algebra of the chain exchanges $R_{r,r+1},R_{n,a},R_{ab}$ without an identity generator, and for every vector $\psi$,
--   $$\widetilde H(\psi\otimes|00\rangle)=((H-\operatorname{Tr}(H)I/2^n)\psi)\otimes|00\rangle,$$
--   $$e^{-it\widetilde H}(\psi\otimes|00\rangle)=e^{i\operatorname{Tr}(H)t/2^n}(e^{-itH}\psi)\otimes|00\rangle\quad(t\in\mathbb R).$$
--   This retains the prescribed construction and its scalar phase rather than introducing an arbitrary implementing Hamiltonian.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 33, Theorem 4: prescribed two-ancilla Hamiltonian lift

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

/-- PDF pp.32–33, Theorem 4, I8/I17/I21–I24. The lift is fully prescribed;
I23's stray subscript is removed. The named last data wire requires n≥1. -/
theorem prescribed_hamiltonian_lift (n : ℕ) (hn : 1 ≤ n) (H : Op n)
    (hH : H.IsHermitian) (hSym : RotationInvariant H) :
    (liftHamiltonian H).IsHermitian ∧
    Complex.I • liftHamiltonian H ∈ exchangeLie (n+2) true false ∧
    (∀ psi : Vec n,
      act (liftHamiltonian H) (tensorState psi (zeroKet 2)) =
        tensorState (act (H-(Matrix.trace H/(2 : ℂ)^n) • (1 : Op n)) psi) (zeroKet 2)) ∧
    (∀ (t : ℝ) (psi : Vec n),
      act (evolve (liftHamiltonian H) t) (tensorState psi (zeroKet 2)) =
        Complex.exp (Complex.I * Matrix.trace H * (t : ℂ)/(2 : ℂ)^n) •
          tensorState (act (evolve H t) psi) (zeroKet 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
