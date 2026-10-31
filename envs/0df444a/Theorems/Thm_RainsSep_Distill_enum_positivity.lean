-- Prove2me | Theorems.Thm_RainsSep_Distill_enum_positivity
-- name    : RainsSep.Distill.enum_positivity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T16:02:51.090167+00:00
-- url     : https://prove2.me/theorems/483dcb29-3bd5-4deb-99c6-c623976c478f
-- title:
--   Eqs. (31)–(32): weight-enumerator and shadow positivity
-- statement:
--   Let $(P^{(1)},P^{(2)})$ be a product Kraus representation of a separable superoperator $\mathcal P$ from two $n$-qubit registers to $W\otimes W$, $\dim W=K$. Then:
--
--   1. the polynomial $B'(u-v,Kv,x-y,2y)$ has nonnegative coefficients;
--   2. the polynomial $B'(v-u,u+v,y-x,x+y)$ (the analogue of the shadow enumerator) has nonnegative coefficients;
--   3. $B'(u-v,Kv,x-y,2y)=u\,B(x,y)+v\big((x+3y)^n-B(x,y)\big)$;
--   4. $B'(v-u,u+v,y-x,x+y)=u\Big(\frac1K(x+3y)^n-S(x,y)\Big)+v\Big(\frac1K(x+3y)^n+S(x,y)\Big)$,
--
--   where $S(x,y)=B\big(\frac{3y-x}{2},\frac{x+y}{2}\big)$. Positivity comes from the positive semidefiniteness of $\overline{\rho_i^{(1)}}$ and $\rho_i^{(2)}$ through the theory of quantum weight enumerators; it is the source of every constraint used in Theorems 1 and 2.
--
--   Differences from the source:
--   - encoding: "nonnegative coefficients" of polynomials in u, v, x, y; B and S polynomials in x, y → HasNonnegCoeffs of MvPolynomial (Fin 4) ℝ; B and S renamed from variables X 0, X 1 to X 2, X 3; reason: the same coefficients
--   - encoding: product Kraus representation Σ_i of Eq. (13), index set unspecified → P₁, P₂ indexed by Fin m; reason: in finite dimension every separable superoperator has a finite product representation (its Choi matrix lies in the finite-dimensional separable cone, Carathéodory), so nothing is excluded
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (31)–(33), p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RainsSep_Distill_polyB
import Definitions.Def_RainsSep_Distill_polyS
import Definitions.Def_RainsSep_Distill_polyBprime
import Definitions.Def_RainsSep_Distill_HasNonnegCoeffs

open QAlgorithms MvPolynomial

namespace RainsSep.Distill

/-- **Eqs. (31)–(32): weight-enumerator and shadow positivity.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eqs. (31)–(33), p. 3: "Since each \overline{ρ_i(1)} and ρ_i(2) is positive semi-definite,
the theory of weight enumerators [6] tells us that the polynomials B′(u − v, Kv, x − y, 2y) and
B′(v − u, u + v, y − x, x + y) have nonnegative coefficients; note that the latter is the analogue
of the "shadow" enumerator, which was shown to be nonnegative in [7]. These polynomials can be
written in terms of B(x, y), using (30): B′(u − v, Kv, x − y, 2y) = uB(x, y) + v((x + 3y)^n −
B(x, y)), (31) B′(v − u, u + v, y − x, x + y) = u((1/K)(x + 3y)^n − S(x, y)) + v((1/K)(x + 3y)^n
+ S(x, y)), (32) where S(x, y) = B((3y − x)/2, (x + y)/2). (33)"

For every product Kraus representation `(P₁, P₂)` of a separable superoperator `P` from `n`
qubit pairs to `ℂ^K ⊗ ℂ^K`:
1. `B′(u − v, Kv, x − y, 2y)` has nonnegative coefficients;
2. `B′(v − u, u + v, y − x, x + y)` has nonnegative coefficients;
3. `B′(u − v, Kv, x − y, 2y) = uB(x, y) + v((x + 3y)ⁿ − B(x, y))`;
4. `B′(v − u, u + v, y − x, x + y) = u((1/K)(x + 3y)ⁿ − S(x, y)) + v((1/K)(x + 3y)ⁿ + S(x, y))`.

**Formalization Note.** Variables `u, v, x, y` are `X 0, …, X 3` of `MvPolynomial (Fin 4) ℝ`;
`B` and `S` (polynomials in `X 0, X 1` of `MvPolynomial (Fin 2) ℝ`) are renamed into
`x = X 2`, `y = X 3`. "Nonnegative coefficients" is coefficientwise (`HasNonnegCoeffs`). -/
theorem enum_positivity {n K m : ℕ} (P₁ P₂ : Fin m → Matrix (Fin K) (Qubits n) ℂ)
    (hP : IsKrausFamily fun i => Matrix.kronecker (P₁ i) (P₂ i)) :
    HasNonnegCoeffs (bind₁ ![X 0 - X 1, C (K : ℝ) * X 1, X 2 - X 3, C 2 * X 3]
        (polyBprime P₁ P₂)) ∧
      HasNonnegCoeffs (bind₁ ![X 1 - X 0, X 0 + X 1, X 3 - X 2, X 2 + X 3]
        (polyBprime P₁ P₂)) ∧
      bind₁ ![X 0 - X 1, C (K : ℝ) * X 1, X 2 - X 3, C 2 * X 3] (polyBprime P₁ P₂) =
        X 0 * rename (![2, 3] : Fin 2 → Fin 4)
            (polyB (krausApply fun i => Matrix.kronecker (P₁ i) (P₂ i))) +
          X 1 * ((X 2 + C 3 * X 3) ^ n - rename (![2, 3] : Fin 2 → Fin 4)
            (polyB (krausApply fun i => Matrix.kronecker (P₁ i) (P₂ i)))) ∧
      bind₁ ![X 1 - X 0, X 0 + X 1, X 3 - X 2, X 2 + X 3] (polyBprime P₁ P₂) =
        X 0 * (C (1 / (K : ℝ)) * (X 2 + C 3 * X 3) ^ n - rename (![2, 3] : Fin 2 → Fin 4)
            (polyS (krausApply fun i => Matrix.kronecker (P₁ i) (P₂ i)))) +
          X 1 * (C (1 / (K : ℝ)) * (X 2 + C 3 * X 3) ^ n + rename (![2, 3] : Fin 2 → Fin 4)
            (polyS (krausApply fun i => Matrix.kronecker (P₁ i) (P₂ i)))) := by sorry

end RainsSep.Distill
