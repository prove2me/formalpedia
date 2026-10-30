-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_permutation_sum_basis
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.permutation_sum_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:15:27.971685+00:00
-- url     : https://prove2.me/theorems/9597dafe-b655-4823-b368-5cbf5b5e561d
-- title:
--   New permutation-sum basis B_m, Eqs.(H5)–(H11)
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Set $B_0=I$ and for physical even $m>0$ let $B_m=(m/2)!^{-1}\sum_{i_1,\ldots,i_m\ \mathrm{distinct}}P_{i_1i_2}\cdots P_{i_{m-1}i_m}$. Then the $B_m$ form another basis of the same complex central space, with
--   $$B_m=\sum_{l=0}^{m}2^{(l-m)/2}\frac{(n-l)!}{(n-m)!((m-l)/2)!}C_l=\sum_jb_m(j)\Pi_j,$$
--   where $b_m(j)$ is the same linear combination of the $c_l(j)$. Terms with $l>m$ are absent. The identity convention supplies the dimension omitted by the paragraph that introduces only $m\ge2$.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 29, New permutation-sum basis B_m, Eqs.(H5)–(H11)

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

/-- PDF pp.29–30, H5–H11: permutation-sum basis, including the missing identity
B_0 supplied by the empty-product convention. -/
theorem permutation_sum_basis (n : ℕ) :
    swapSum n 0 = 1 ∧
    LinearIndependent ℂ (fun r : Spin n => swapSum n (2*r.val)) ∧
    Submodule.span ℂ (Set.range fun r : Spin n => swapSum n (2*r.val)) =
      Submodule.span ℂ (Set.range fun r : Spin n => central n (2*r.val)) ∧
    ∀ m : ℕ, ValidBody n m →
      swapSum n m = ∑ r : Fin (m/2+1),
        (permutationSumCoefficient n m (2*r.val) : ℂ) • central n (2*r.val) ∧
      swapSum n m = ∑ j : Spin n,
        ((∑ r : Fin (m/2+1), permutationSumCoefficient n m (2*r.val)*centralEigenvalue n (2*r.val) j) : ℂ) •
          spinProjector n j := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
