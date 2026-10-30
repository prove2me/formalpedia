-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_central_recurrence
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.central_recurrence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:01:34.970971+00:00
-- url     : https://prove2.me/theorems/89430146-aba4-4064-b010-f937ba9f97b2
-- title:
--   Recursive relation for C_l and c_l(j), Eqs.(B43)–(B45)
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $l$ be even with $2\le l$ and $l+2\le2\lfloor n/2\rfloor$. Then
--   $$C_2C_l=(l/2+1)C_{l+2}+l(n-l-1)C_l+\binom{n-l+2}{2}(l+1)C_{l-2},$$
--   $$c_{l+2}(j)=\frac{2j(j+1)-l(n-l-1)-3n/2}{l/2+1}c_l(j)-\frac{\binom{n-l+2}{2}(l+1)}{l/2+1}c_{l-2}(j).$$
--   The initial values are $c_0(j)=1$ and $c_2(j)=2j(j+1)-3n/2$. This is the final recurrence of B43–B45, not the erroneous intermediate B36.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 15, Recursive relation for C_l and c_l(j), Eqs.(B43)–(B45)

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

/-- PDF pp.12–15, B43–B45: the final recurrence, in the physical interior range.
B36 has a printed typo; the final B43–B45 are used. -/
theorem central_recurrence (n l : ℕ) (hl : Even l) (hlo : 2 ≤ l)
    (hhi : l+2 ≤ 2*(n/2)) :
    central n 2 * central n l =
      ((l/2+1 : ℕ) : ℂ) • central n (l+2) +
      (((n : ℂ)-(l : ℂ)-1)*(l : ℂ)) • central n l +
      ((Nat.choose (n-l+2) 2 : ℂ)*(l+1 : ℕ)) • central n (l-2) ∧
    (∀ j : Spin n, centralEigenvalue n (l+2) j =
      ((2*spin n j*(spin n j+1) - (l : ℝ)*((n : ℝ)-l-1)-3*(n : ℝ)/2) /
        (l/2+1 : ℕ)) * centralEigenvalue n l j -
      ((Nat.choose (n-l+2) 2 : ℝ)*(l+1 : ℕ)/(l/2+1 : ℕ)) * centralEigenvalue n (l-2) j) ∧
    (∀ j : Spin n, centralEigenvalue n 0 j = 1 ∧
      centralEigenvalue n 2 j = 2*spin n j*(spin n j+1)-3*(n : ℝ)/2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
