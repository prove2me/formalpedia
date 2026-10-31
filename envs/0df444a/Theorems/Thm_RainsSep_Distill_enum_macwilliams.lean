-- Prove2me | Theorems.Thm_RainsSep_Distill_enum_macwilliams
-- name    : RainsSep.Distill.enum_macwilliams
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T16:01:36.777847+00:00
-- url     : https://prove2.me/theorems/467035fb-e099-4d7d-a33e-be84e6e2d4ea
-- title:
--   Eq. (25): $B'(1,0,x-y,2y)=B(x,y)$
-- statement:
--   Let $\mathcal P(\rho)=\sum_i(P_i^{(1)}\otimes P_i^{(2)})\rho(P_i^{(1)}\otimes P_i^{(2)})^\dagger$ be a product Kraus representation of a separable superoperator from two $n$-qubit registers $V\otimes V$ to $W\otimes W$, $\dim W=K$. Then, as polynomials in $x,y$,
--
--   $$
--   B'(1,0,x-y,2y)=B(x,y)=\sum_i B_i(\mathcal P)\,x^{n-i}y^i .
--   $$
--
--   This MacWilliams-type identity links the fidelity enumerator $B$ to the partial-trace enumerator $B'$, whose coefficients are traces of products of positive operators.
--
--   Differences from the source:
--   - encoding: B′_S defined through partial traces Tr_S; S ⊂ {1,…,n}, W indexed by 0 → B′_S through the explicit index sum trPairS; qubits Fin n, W the label none; polynomial identity in MvPolynomial; reason: the same numbers and the same polynomial
--   - encoding: product Kraus representation Σ_i of Eq. (13), index set unspecified → P₁, P₂ indexed by Fin m; reason: in finite dimension every separable superoperator has a finite product representation (its Choi matrix lies in the finite-dimensional separable cone, Carathéodory), so nothing is excluded
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (23)–(25), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RainsSep_Distill_polyB
import Definitions.Def_RainsSep_Distill_polyBprime

open QAlgorithms MvPolynomial

namespace RainsSep.Distill

/-- **Eq. (25): `B′(1, 0, x − y, 2y) = B(x, y)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eqs. (23)–(25), p. 2: "We can then define a polynomial B′(u, v, x, y) = … (24) The
arguments in [6] tell us that B′(1, 0, x − y, 2y) = B(x, y) = Σ_i B_i(P) x^{n−i} y^i. (25)"

For every product Kraus representation `P(ρ) = Σ_i (P₁ i ⊗ P₂ i) ρ (P₁ i ⊗ P₂ i)†` of a
separable superoperator from `n` qubit pairs to `ℂ^K ⊗ ℂ^K` (Eq. (13)), substituting
`u = 1, v = 0, x ↦ x − y, y ↦ 2y` into `B′` gives `B(x, y)`, as polynomials in `x = X 0`,
`y = X 1`.

**Formalization Note.** Polynomial identity in `MvPolynomial (Fin 2) ℝ`; `B′`'s variables
`u, v, x, y` are `X 0, …, X 3`. -/
theorem enum_macwilliams {n K m : ℕ} (P₁ P₂ : Fin m → Matrix (Fin K) (Qubits n) ℂ)
    (hP : IsKrausFamily fun i => Matrix.kronecker (P₁ i) (P₂ i)) :
    bind₁ ![1, 0, X 0 - X 1, C 2 * X 1] (polyBprime P₁ P₂) =
      polyB (krausApply fun i => Matrix.kronecker (P₁ i) (P₂ i)) := by sorry

end RainsSep.Distill
