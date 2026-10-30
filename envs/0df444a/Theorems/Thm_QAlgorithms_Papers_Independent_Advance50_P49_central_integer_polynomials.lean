-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_central_integer_polynomials
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.central_integer_polynomials
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:59:37.423981+00:00
-- url     : https://prove2.me/theorems/32d081f2-275a-4f6a-919c-1a94b0b3989c
-- title:
--   Integer eigenvalues and polynomial dependence on total spin
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For every physical even $l$ and legal spin $j$, the multiplicity $m(n,j)$ is positive and $c_l(j)$ is an integer, with
--   $$c_l(j)=\frac{n!}{(n-l)!\,2^{l/2}(l/2)!}\sum_{r=0}^{l/2}\binom{l/2}{r}(-4)^r\frac{m(n-2r,j)}{m(n,j)}.$$
--   Here $m(N,j)=\binom{N}{N/2-j}(2j+1)/(N/2+j+1)$ on the legal spectrum and is zero otherwise. There exists a nonzero real polynomial $p_l$ of exact degree $l/2$ satisfying $C_l=p_l(J^2)$ and $c_l(j)=p_l(j(j+1))$. At $l=0$ take $p_0=1$, and at $l=2$ take $p_2(x)=2x-3n/2$. Integer-valued refers to legal spins, not to integer polynomial coefficients.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 11, Integer eigenvalues and polynomial dependence on total spin

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

/-- PDF pp.2,11–13, B22c and B2: integer values on legal spins, and an exact-degree
real polynomial in j(j+1), also evaluated at the actual J². -/
theorem central_integer_polynomials (n : ℕ) :
    ∀ l : ℕ, ValidBody n l →
      (∀ j : Spin n, 0 < spinMultiplicity n (n-2*j.val) ∧
        centralEigenvalue n l j = (eigenInt n l j : ℝ) ∧
        centralEigenvalue n l j =
          (Nat.factorial n : ℝ) /
            ((Nat.factorial (n-l) : ℝ) * (2 : ℝ)^(l/2) * (Nat.factorial (l/2) : ℝ)) *
          ∑ r ∈ Finset.range (l/2+1),
            (Nat.choose (l/2) r : ℝ) * (-4 : ℝ)^r *
              (spinMultiplicity (n-2*r) (n-2*j.val) : ℝ) /
                (spinMultiplicity n (n-2*j.val) : ℝ)) ∧
      ∃ p : Polynomial ℝ, p ≠ 0 ∧ p.natDegree = l/2 ∧
        central n l = Polynomial.aeval (casimir n) p ∧
        (∀ j : Spin n, centralEigenvalue n l j = p.eval (spin n j * (spin n j+1))) ∧
        (l = 0 → p = 1) ∧
        (l = 2 → p = Polynomial.C 2 * Polynomial.X - Polynomial.C (3*(n : ℝ)/2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
