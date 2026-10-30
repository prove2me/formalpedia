-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_single_ancilla_obstruction
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.single_ancilla_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:21:14.487881+00:00
-- url     : https://prove2.me/theorems/de48bffd-d24d-4c30-a7ce-b61c0aba90ed
-- title:
--   One ancilla cannot give universality below the locality threshold
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Suppose invariant unitary $V$ can be implemented using $\mathcal V_k$ on $n+1$ qubits with fixed pure normalized one-qubit ancillary input and output. Then for every even $l>k$,
--   $$2\Phi_l(V)=0\pmod{2\pi}.$$
--   For $n\ge4$ and $2\le k<2\lfloor n/2\rfloor$, there exists an invariant unitary admitting no such implementation. More precisely, the implementable family lies inside a closed subset with empty interior in the invariant-unitary group. Thus one ancilla does not restore universality below this threshold. Values $\Phi_l=\pi$ are allowed by the necessary condition and are not incorrectly excluded.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 36, One ancilla cannot give universality below the locality threshold

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

/-- PDF pp.4,36, J9: doubled phases, not nonzero phases alone. The obstruction
for exchanges begins at n=4, since n≤3 has no missing positive even weight. -/
theorem single_ancilla_obstruction (n k : ℕ) :
    (∀ V : Op n, SymUnitary V → OneAncillaReachable k V →
      ∀ l : ℕ, Even l → k<l → (2 : ℕ) • bodyPhase V l=0) ∧
    (4 ≤ n → 2 ≤ k → k<2*(n/2) →
      ∃ V : Op n, SymUnitary V ∧ ¬OneAncillaReachable k V) ∧
    (4 ≤ n → 2 ≤ k → k<2*(n/2) →
      ∃ s : Set {V : Op n // SymUnitary V}, IsClosed s ∧ interior s=∅ ∧
        ∀ V : {V : Op n // SymUnitary V}, OneAncillaReachable k V.val → V∈s) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
