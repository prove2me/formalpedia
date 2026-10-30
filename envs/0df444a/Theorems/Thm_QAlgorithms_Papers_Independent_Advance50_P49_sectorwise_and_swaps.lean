-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_sectorwise_and_swaps
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.sectorwise_and_swaps
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:03:46.740769+00:00
-- url     : https://prove2.me/theorems/5c4ecc11-e593-4697-b993-a3c2fbc83579
-- title:
--   Lemma 1: sectorwise universality plus swaps implies independent special blocks
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $\mathcal Y$ be any subgroup of the invariant unitary group. Suppose that for each legal $j$ and each invariant unitary $V$, there are $Y_j\in\mathcal Y$ and a real $\theta$ such that $V\Pi_j=e^{i\theta}Y_j\Pi_j$. Suppose also that, for each distinct pair $a,b$, some phase multiple of the physical swap $P_{ab}$ belongs to $\mathcal Y$. Then
--   $$S\mathcal V_n\subseteq\mathcal Y,$$
--   and every invariant $V$ can be written $V=(\sum_je^{i\theta_j}\Pi_j)Y$ with $Y\in\mathcal Y$ and $\theta_j\in[0,2\pi)$. The sectorwise witnesses may depend on both $j$ and $V$. No closedness or Lie-subgroup hypothesis is imposed.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 18, Lemma 1: sectorwise universality plus swaps implies independent special blocks

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

/-- PDF p.18, Lemma 1: an arbitrary subgroup, represented by a unitary submonoid
closed under adjoint. No topological closedness hypothesis is added. -/
theorem sectorwise_and_swaps (n : ℕ) (Y : Submonoid (Op n))
    (hUnitary : ∀ U : Op n, U ∈ Y → SymUnitary U)
    (hInverse : ∀ U : Op n, U ∈ Y → Uᴴ ∈ Y)
    (hSector : ∀ (j : Spin n) (V : Op n), SymUnitary V →
      ∃ (W : Op n) (theta : ℝ), W ∈ Y ∧
        V*spinProjector n j = Complex.exp (Complex.I*theta) • (W*spinProjector n j))
    (hSwaps : ∀ a b : Fin n, a ≠ b →
      ∃ theta : ℝ, Complex.exp (Complex.I*theta) • wireSwap a b ∈ Y) :
    (∀ V : Op n, Special V → V ∈ Y) ∧
    (∀ V : Op n, SymUnitary V →
      ∃ (theta : Spin n → ℝ) (W : Op n), W ∈ Y ∧
        (∀ j, 0 ≤ theta j ∧ theta j < 2*Real.pi) ∧
        V = sectorPhases n theta * W) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
