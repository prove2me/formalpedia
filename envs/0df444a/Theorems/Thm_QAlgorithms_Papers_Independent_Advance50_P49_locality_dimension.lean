-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_locality_dimension
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.locality_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:04:47.084576+00:00
-- url     : https://prove2.me/theorems/32d287db-4a01-43e7-96f1-0eb9066b4f0f
-- title:
--   Dimension of V_k and v_k, Eq.(6), Appendix D
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For $2\le k\le n$, let $d_k=\dim_{\mathbb R}\mathfrak v_k$, equivalently the dimension of the connected Lie group $\mathcal V_k$. Then
--   $$d_k+\lfloor n/2\rfloor=\frac{\binom{2n}{n}}{n+1}+\lfloor k/2\rfloor,\qquad \dim Z(\mathfrak v_k)=\lfloor k/2\rfloor+1.$$
--   Also $\mathfrak v_k=\mathfrak{sv}_n\oplus Z(\mathfrak v_k)$, with trivial intersection, and $d_n=\sum_jm(n,j)^2$, $(n+1)d_n=\binom{2n}{n}$. Hence $\mathcal V_k=\mathcal V_n$ exactly when $\lfloor k/2\rfloor=\lfloor n/2\rfloor$. The subgroup $\mathcal V_k$ is closed; every invariant unitary outside it has an open neighborhood disjoint from it. The additive dimension equation avoids truncated natural subtraction.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 3, Dimension of V_k and v_k, Eq.(6), Appendix D

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

/-- PDF pp.3,20–21, Eq.6 and Appendix D: the real Lie dimension (hence the
connected Lie-group dimension), direct sum, and exact universality threshold. -/
theorem locality_dimension (n k : ℕ) (hlo : 2 ≤ k) (hhi : k ≤ n) :
    (Module.finrank ℝ (localLie n k) : ℤ) + (n/2 : ℕ) =
      (Nat.choose (2*n) n : ℤ)/(n+1 : ℕ) + (k/2 : ℕ) ∧
    Module.finrank ℝ (centralSpace n k) = k/2+1 ∧
    Module.finrank ℝ (localLie n n) =
      ∑ j : Spin n, spinMultiplicity n (n-2*j.val)^2 ∧
    Module.finrank ℝ (localLie n n) * (n+1) = Nat.choose (2*n) n ∧
    (localLie n k).toSubmodule = specialLie n n ⊔ centralSpace n k ∧
    Disjoint (specialLie n n) (centralSpace n k) ∧
    ((∀ V : Op n, SymUnitary V → V ∈ localGroup n k) ↔ k/2=n/2) ∧
    IsClosed (localGroup n k : Set (Op n)) ∧
    (∀ V : Op n, SymUnitary V → V ∉ localGroup n k →
      ∃ s : Set (Op n), IsOpen s ∧ V ∈ s ∧ Disjoint s (localGroup n k : Set (Op n))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
