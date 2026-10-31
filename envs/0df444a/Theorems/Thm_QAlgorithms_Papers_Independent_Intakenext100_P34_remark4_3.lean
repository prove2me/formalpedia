-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_remark4_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.remark4_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:08:55.928029+00:00
-- url     : https://prove2.me/theorems/9382d444-7c24-42d7-86c3-419aa778ff24
-- title:
--   The degenerate rank-two contraction ideal and its center action
-- statement:
--   Let $C$ be a commutative unital ring in which $2$ is invertible, let $\epsilon\in\{1,-1\}$, and fix scalars $z_0^{(\ell)}\in C$ for all $\ell\ge0$. Write $\mathcal W_k$ for the actual quotient defined by (2.1)–(2.5) and (2.21)–(2.24), and $z_0(u)=\sum_{\ell\ge0}z_0^{(\ell)}u^{-\ell}$.
--
--   For the center statements, specialize $\kappa_0,\kappa_1$ to scalars and assume the identity
--   $$
--   (z_0(-u)-\tfrac12-\epsilon u)(z_0(u)-\tfrac12+\epsilon u)=(\tfrac12-\epsilon u)(\tfrac12+\epsilon u).
--   $$
--
--   Assume also $C\ne0$ and work at level two. Then
--   $$
--   \mathcal W_2e_1=C[y_1]e_1,\qquad
--   \{y_1^ne_1:n\ge0\}\text{ is linearly independent over }C.
--   $$
--   Every central element acts on this entire left ideal as multiplication by a scalar in $C$, and
--   $$
--   \mathcal W_2\text{ is not a finitely generated }Z(\mathcal W_2)\text{-module}.
--   $$
--   The ideal equality together with independence gives the exhibited infinite free $C$-basis. This is the ring-valued meaning of the source's infinite-dimensional assertion.
--
--   The unquantified parenthetical generic-irreducibility claim is recorded separately as a source-ambiguity gap; it is not a hypothesis or an asserted conclusion here.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 22, Remark 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Remark 4.3, PDF p.22: the ideal, its free indexed family, scalar
center action, and failure of finite generation over the center.
The unpinned generic-irreducibility parenthetical is documented in the audit. -/
theorem remark4_3 [Nontrivial C] (P : DParams C)
    (hscalar : P.scalarKappa.isSome) (hadm : DAdmissible C P) :
    let j : Adj 2 := ⟨0, by decide⟩
    let e := dwMap C P 2 (de C j)
    let y := dwMap C P 2 (dy C (adjacentLeft j))
    leftMultiples e = {a | ∃ p : Polynomial C,
      a = Polynomial.eval₂ (algebraMap C (DW C P 2)) y p * e} ∧
    LinearIndependent C (fun n : ℕ => y^n*e) ∧
    (∀ c : DW C P 2, Central c → ∃ s : C,
      ∀ a ∈ leftMultiples e, c*a = algebraMap C (DW C P 2) s*a) ∧
    ¬ Module.Finite (Subalgebra.center C (DW C P 2)) (DW C P 2) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
