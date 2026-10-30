-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_odd_time_reversal
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.odd_time_reversal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:07:11.714827+00:00
-- url     : https://prove2.me/theorems/4be9409c-0fdb-4ad9-aa1d-1b7354a8be23
-- title:
--   Odd time-reversal parity and exchange reachability
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $\Theta=Y^{\otimes n}K$, up to an irrelevant scalar, be spin-half time reversal, with $K$ complex conjugation in the physical basis. If $H$ is Hermitian and $\Theta H\Theta^{-1}=-H$, then
--   $$\operatorname{Tr}(H\Pi_j)=0\quad\text{for all legal }j,\qquad \operatorname{Tr}(HC_l)=0\quad\text{for all physical even }l.$$
--   If $H$ is also rotationally invariant, then $iH$ lies in the exchange-generated algebra and $e^{-itH}$ is exchange-realizable for all real $t$. This corrects the source's unrestricted final implementation sentence: one-qubit $Z$ is odd under time reversal but is not invariant.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 23, Odd time-reversal parity and exchange reachability

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

/-- PDF p.23, F4–F5 and following paragraph. The printed final realizability
sentence needs rotational invariance; one-qubit Z is a counterexample without it. -/
theorem odd_time_reversal (n : ℕ) (H : Op n) (hH : H.IsHermitian)
    (hOdd : reverseTime H = -H) :
    (∀ j : Spin n, Matrix.trace (H*spinProjector n j)=0) ∧
    (∀ l : ℕ, ValidBody n l → Matrix.trace (H*central n l)=0) ∧
    (RotationInvariant H → Complex.I • H ∈ exchangeLie n false false ∧
      ∀ t : ℝ, evolve H t ∈ exchangeGroup n false false) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
