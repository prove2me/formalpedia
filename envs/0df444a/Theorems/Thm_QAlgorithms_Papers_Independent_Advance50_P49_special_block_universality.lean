-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_special_block_universality
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.special_block_universality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:03:05.325712+00:00
-- url     : https://prove2.me/theorems/fba3e46d-0712-4868-b32e-5ae541ca0593
-- title:
--   Theorem 2: exchange universality on the special-unitary blocks
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   If $H_0$ is Hermitian and invariant with $\operatorname{Tr}(H_0\Pi_j)=0$ for every legal $j$, then $iH_0\in\mathfrak v_k$ for all $k\ge2$ and $e^{-itH_0}$ is exchange-realizable for every real $t$. If $Y\simeq\bigoplus_jI_{2j+1}\otimes y_j$ is invariant and unitary with $\det y_j=1$ for every $j$, then $Y$ is exchange-realizable and belongs to $\mathcal V_2$. Consequently,
--   $$S\mathcal V_2=S\mathcal V_n,\qquad \mathfrak{sv}_2=\mathfrak{sv}_n,$$
--   and every invariant unitary admits
--   $$V=\left(\sum_je^{i\theta_j}\Pi_j\right)Y,\quad 0\le\theta_j<2\pi,\quad Y\in S\mathcal V_2.$$
--   Here $S\mathcal V$ means determinant one on the multiplicity blocks; no uniqueness is asserted.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 17, Theorem 2: exchange universality on the special-unitary blocks

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

/-- PDF pp.17–18, Theorem 2 and C14–C17. Multiplicity-block determinants,
Hamiltonian and group formulations, and existence of the phase decomposition. -/
theorem special_block_universality (n : ℕ) :
    (∀ H : Op n, H.IsHermitian → RotationInvariant H →
      (∀ j : Spin n, Matrix.trace (H*spinProjector n j)=0) →
      (∀ k : ℕ, 2 ≤ k → Complex.I • H ∈ localLie n k) ∧
      (∀ t : ℝ, evolve H t ∈ exchangeGroup n false false ∧
        evolve H t ∈ localGroup n 2)) ∧
    (∀ Y : Op n, Special Y → Y ∈ localGroup n 2 ∧ Y ∈ exchangeGroup n false false) ∧
    ({Y : Op n | Special Y ∧ Y ∈ localGroup n 2} = {Y | Special Y}) ∧
    specialLie n 2 = specialLie n n ∧
    (∀ V : Op n, SymUnitary V →
      ∃ (theta : Spin n → ℝ) (Y : Op n),
        (∀ j, 0 ≤ theta j ∧ theta j < 2*Real.pi) ∧
        Special Y ∧ Y ∈ localGroup n 2 ∧ V = sectorPhases n theta * Y) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
