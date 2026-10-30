-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_central_basis
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.central_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:58:41.470425+00:00
-- url     : https://prove2.me/theorems/49b0786c-c9e6-4c79-a631-7c4d04db47e9
-- title:
--   Central orthogonal basis, spectral expansion, and locality orthogonality
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   The physical operators $C_l$, $0\le l\le2\lfloor n/2\rfloor$, form a complex basis of the simultaneous rotation and permutation commutant. They are Hermitian, belong to the span of $l$-supported terms, and have $\operatorname{Tr}(C_l^2)>0$. Moreover,
--   $$C_l=\sum_jc_l(j)\Pi_j,\qquad \operatorname{Tr}(C_lC_s)=\sum_j\operatorname{Tr}(\Pi_j)c_l(j)c_s(j)=\delta_{ls}\operatorname{Tr}(C_l^2),$$
--   $$\Pi_j=\sum_l\frac{\operatorname{Tr}(\Pi_j C_l)}{\operatorname{Tr}(C_l^2)}C_l.$$
--   Every sector has positive trace. If $A$ is supported on fewer than $l$ wires, $\operatorname{Tr}(AC_l)=0$. For $Q_s=R_{12}\cdots R_{s-1,s}$, including $Q_0=I$,
--   $$\operatorname{Tr}(Q_sC_l)=\delta_{sl}\frac{(n-s)!(s/2)!}{n!}\operatorname{Tr}(C_l^2).$$
--   These identities identify the actual central basis and its dual expansion.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 10, Central orthogonal basis, spectral expansion, and locality orthogonality

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

/-- PDF pp.2,10–12, B3–B6/B25–B27: physical orthogonal central basis,
nonzero norms, spectral expansion and orthogonality to lower support. -/
theorem central_basis (n : ℕ) :
    central n 0 = 1 ∧
    LinearIndependent ℂ (fun r : Spin n => central n (2*r.val)) ∧
    ((Submodule.span ℂ (Set.range fun r : Spin n => central n (2*r.val)) : Set (Op n)) =
      {A | RotationInvariant A ∧ ∀ p : Equiv.Perm (Fin n), A * wirePermutation p = wirePermutation p * A}) ∧
    (∀ l : ℕ, ValidBody n l →
      (central n l).IsHermitian ∧ 0 < (Matrix.trace (central n l ^ 2)).re ∧
      central n l ∈ localSum n l ∧
      central n l = ∑ j : Spin n, (centralEigenvalue n l j : ℂ) • spinProjector n j ∧
      ∀ (A : Op n) (s : Finset (Fin n)), WireSupported s A → s.card < l →
        Matrix.trace (A * central n l) = 0) ∧
    (∀ l s : ℕ, ValidBody n l → ValidBody n s →
      Matrix.trace (central n l * central n s) =
        ∑ j : Spin n, Matrix.trace (spinProjector n j) *
          (centralEigenvalue n l j : ℂ) * (centralEigenvalue n s j : ℂ) ∧
      Matrix.trace (central n l * central n s) =
        if l = s then Matrix.trace (central n l ^ 2) else 0) ∧
    (∀ j : Spin n, 0 < (Matrix.trace (spinProjector n j)).re ∧
      spinProjector n j = ∑ r : Spin n,
        (Matrix.trace (spinProjector n j * central n (2*r.val)) /
          Matrix.trace (central n (2*r.val) ^ 2)) • central n (2*r.val)) ∧
    (∀ s l : ℕ, ValidBody n s → ValidBody n l →
      Matrix.trace (standardQ n s * central n l) =
        if s = l then ((Nat.factorial (n-s) : ℂ) * (Nat.factorial (s/2) : ℂ) /
          (Nat.factorial n : ℂ)) * Matrix.trace (central n l ^ 2) else 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
