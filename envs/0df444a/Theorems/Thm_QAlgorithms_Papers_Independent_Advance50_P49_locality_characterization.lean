-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_locality_characterization
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.locality_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:57:56.633499+00:00
-- url     : https://prove2.me/theorems/e90f8f45-8bfb-4ed1-b7d1-9d5bf751eed5
-- title:
--   Theorem 1: exact locality characterization of Hamiltonians
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $H$ be Hermitian and invariant, and let $k\ge2$, with no upper bound on $k$. Then
--   $$[\forall t\in\mathbb R,\ e^{-itH}\in\mathcal V_k]\iff[\forall l>k,\ l\le2\lfloor n/2\rfloor:\ \operatorname{Tr}(HC_l)=\sum_j c_l(j)\operatorname{Tr}(H\Pi_j)=0].$$
--   Equivalently, $\mathfrak v_k=\{A\in\mathfrak v_n:\operatorname{Tr}(AC_l)=0\text{ for every such }l\}$. This characterizes Hamiltonian reachability at every time, including the empty constraint range when $k>n$.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 2, Theorem 1: exact locality characterization of Hamiltonians

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

/-- PDF p.2, Theorem 1; pp.16–17, C1/C4. All times, not a single endpoint.
k>n is permitted and leaves no high-body constraints. -/
theorem locality_characterization (n k : ℕ) (hk : 2 ≤ k) (H : Op n)
    (hH : H.IsHermitian) (hSym : RotationInvariant H) :
    ((∀ t : ℝ, evolve H t ∈ localGroup n k) ↔
      ∀ l : ℕ, ValidBody n l → k < l →
        Matrix.trace (H * central n l) =
          ∑ j : Spin n, (centralEigenvalue n l j : ℂ) * Matrix.trace (H * spinProjector n j) ∧
        Matrix.trace (H * central n l) = 0) ∧
    ((localLie n k : Set (Op n)) =
      {A | A ∈ localLie n n ∧ ∀ l : ℕ, ValidBody n l → k < l →
        Matrix.trace (A * central n l) = 0}) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
