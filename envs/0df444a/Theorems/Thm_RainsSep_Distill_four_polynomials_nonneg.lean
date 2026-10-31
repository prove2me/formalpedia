-- Prove2me | Theorems.Thm_RainsSep_Distill_four_polynomials_nonneg
-- name    : RainsSep.Distill.four_polynomials_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T16:02:49.408072+00:00
-- url     : https://prove2.me/theorems/318492c3-0194-469c-b9c2-b617c56d7353
-- title:
--   Eqs. (33)–(34): four polynomials with nonnegative coefficients and $0\le F_{\mathcal P}(E)\le 1$
-- statement:
--   Let $\mathcal P$ be a separable superoperator from two $n$-qubit registers to $W\otimes W$, $\dim W=K$. Then each of the four polynomials
--
--   $$
--   B(x,y),\qquad (x+3y)^n-B(x,y),\qquad \tfrac1K(x+3y)^n-S(x,y),\qquad \tfrac1K(x+3y)^n+S(x,y)
--   $$
--
--   has nonnegative coefficients, and $0\le F_{\mathcal P}(E)\le 1$ for every $n$-qubit Pauli product $E$ (Eq. (34)).
--
--   The first two say $0\le B_j(\mathcal P)\le\binom nj3^j$; the third, evaluated at suitable nonnegative $x,y$, gives Theorem 1.
--
--   Differences from the source:
--   - encoding: a separable superoperator has a product Kraus representation Σ_i (unspecified index set) → IsSeparableSuperop asks for a finite product Kraus family indexed by Fin m; reason: in finite dimension every separable superoperator has a finite product representation (its Choi matrix lies in the finite-dimensional separable cone, Carathéodory), so nothing is excluded
--   - encoding: "for all E", E a tensor product of matrices from {1, σx, σy, σz} → for all labels o : Fin n → Pauli (phase-+1 products); reason: the same set of operators
--   - encoding: polynomials in x, y → MvPolynomial (Fin 2) ℝ with x = X 0, y = X 1; S the substitution bind₁ into polyB; reason: the same coefficients
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (33)–(34), p. 3

import Mathlib
import Definitions.Def_RainsSep_Distill_IsSeparableSuperop
import Definitions.Def_RainsSep_Distill_polyB
import Definitions.Def_RainsSep_Distill_polyS
import Definitions.Def_RainsSep_Distill_HasNonnegCoeffs

open QAlgorithms MvPolynomial

namespace RainsSep.Distill

/-- **Eqs. (33)–(34): four polynomials with nonnegative coefficients, and `0 ≤ F_P(E) ≤ 1`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, p. 3: "Since both of those polynomials have nonnegative coefficients, we can conclude that
the four polynomials B(x, y), (x + 3y)^n − B(x, y), (1/K)(x + 3y)^n − S(x, y), (1/K)(x + 3y)^n
+ S(x, y), each have nonnegative coefficients. The first two polynomials simply correspond to the
fact that 0 ≤ F_P(E) ≤ 1 (34) for all E."

For every separable superoperator `P` from `n` qubit pairs to `ℂ^K ⊗ ℂ^K`, the polynomials
`B(x, y)`, `(x + 3y)ⁿ − B(x, y)`, `(1/K)(x + 3y)ⁿ − S(x, y)` and `(1/K)(x + 3y)ⁿ + S(x, y)` have
nonnegative coefficients, and `0 ≤ F_P(E) ≤ 1` for every `n`-qubit Pauli product `E`.

**Formalization Note.** Polynomials in `x = X 0`, `y = X 1` of `MvPolynomial (Fin 2) ℝ`. -/
theorem four_polynomials_nonneg {n K : ℕ}
    (P : Superop (Qubits n × Qubits n) (Fin K × Fin K)) (hP : IsSeparableSuperop P) :
    HasNonnegCoeffs (polyB P) ∧
      HasNonnegCoeffs ((X 0 + C 3 * X 1) ^ n - polyB P) ∧
      HasNonnegCoeffs (C (1 / (K : ℝ)) * (X 0 + C 3 * X 1) ^ n - polyS P) ∧
      HasNonnegCoeffs (C (1 / (K : ℝ)) * (X 0 + C 3 * X 1) ^ n + polyS P) ∧
      ∀ o : Fin n → Stabilizer.Pauli, 0 ≤ pauliFid P o ∧ pauliFid P o ≤ 1 := by sorry

end RainsSep.Distill
