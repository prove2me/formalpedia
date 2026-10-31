-- Prove2me | Theorems.Thm_RainsSep_Distill_enum_traced_W
-- name    : RainsSep.Distill.enum_traced_W
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T16:01:19.611781+00:00
-- url     : https://prove2.me/theorems/50aed6b7-0b68-4ae8-aae3-7cf804249255
-- title:
--   Eqs. (29)–(30): $B'_{\{0\}\cup S}=2^{|S|}/K$ and $B'=uB(x+\tfrac y2,\tfrac y2)+v(x+2y)^n/K$
-- statement:
--   Let $(P^{(1)},P^{(2)})$ be a product Kraus representation of a separable superoperator $\mathcal P$ from two $n$-qubit registers to $W\otimes W$, $\dim W=K$. Then:
--
--   1. for every set $S$ of qubits, $B'_{\{0\}\cup S}(\mathcal P)=2^{|S|}/K$;
--   2. as polynomials,
--
--   $$
--   B'(u,v,x,y)=u\,B\Big(x+\frac y2,\frac y2\Big)+v\,\frac{(x+2y)^n}{K}.
--   $$
--
--   The $v$-part of $B'$ is fixed by trace preservation alone; only the $u$-part carries information about $\mathcal P$.
--
--   Differences from the source:
--   - encoding: {0} ∪ S for S ⊂ {1,…,n} → insert none (S.map some) for S a finite set of Fin n; B(x + y/2, y/2) as a substitution bind₁ into polyB; reason: the same sets and the same polynomial
--   - encoding: product Kraus representation Σ_i of Eq. (13), index set unspecified → P₁, P₂ indexed by Fin m; reason: in finite dimension every separable superoperator has a finite product representation (its Choi matrix lies in the finite-dimensional separable cone, Carathéodory), so nothing is excluded
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (26)–(30), pp. 2–3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RainsSep_Distill_polyB
import Definitions.Def_RainsSep_Distill_polyBprime

open QAlgorithms MvPolynomial

namespace RainsSep.Distill

/-- **Eqs. (29)–(30): `B′_{{0}∪S}(P) = 2^{|S|}/K` and `B′ = uB(x + y/2, y/2) + v(x + 2y)ⁿ/K`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eqs. (26)–(30), pp. 2–3: "Since P is a superoperator, (12) tells us that Σ_i Tr_{W⊗W}(ρ_i(1)
⊗ ρ_i(2)) = Id(V ⊗ V). (28) It follows that B′_{0}∪S(P) = 2^{|S|}/K, (29) and thus that
B′(u, v, x, y) = uB(x + y/2, y/2) + v(x + 2y)^n/K. (30)"

For every product Kraus representation `(P₁, P₂)` of a separable superoperator `P` from `n`
qubit pairs to `ℂ^K ⊗ ℂ^K`:
1. for every set `S` of qubits, `B′_{{0}∪S}(P) = 2^{|S|}/K`;
2. `B′(u, v, x, y) = u·B(x + y/2, y/2) + v·(x + 2y)ⁿ/K` as polynomials.

**Formalization Note.** `{0} ∪ S` is `insert none (S.map some)` (`none` is `W`). Variables
`u, v, x, y` are `X 0, …, X 3` of `MvPolynomial (Fin 4) ℝ`; `B(x + y/2, y/2)` is
`bind₁ ![X 2 + X 3/2, X 3/2] (polyB P)`. -/
theorem enum_traced_W {n K m : ℕ} (P₁ P₂ : Fin m → Matrix (Fin K) (Qubits n) ℂ)
    (hP : IsKrausFamily fun i => Matrix.kronecker (P₁ i) (P₂ i)) :
    (∀ S : Finset (Fin n),
        enumBprime P₁ P₂ (insert none (S.map Function.Embedding.some)) =
          (2 : ℝ) ^ S.card / K) ∧
      polyBprime P₁ P₂ =
        X 0 * bind₁ ![X 2 + C (1 / 2) * X 3, C (1 / 2) * X 3]
            (polyB (krausApply fun i => Matrix.kronecker (P₁ i) (P₂ i))) +
          X 1 * C (1 / (K : ℝ)) * (X 2 + C 2 * X 3) ^ n := by sorry

end RainsSep.Distill
