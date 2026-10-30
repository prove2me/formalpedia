-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_contraction_and_block_positivity
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.contraction_and_block_positivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:45:31.827772+00:00
-- url     : https://prove2.me/theorems/a9e7b06d-6d49-40e2-bbfa-d464210dd8fe
-- title:
--   Eqs.(57)–(59): operator contraction and block positivity
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $r\ge1$ and let $P$ be any operator on $(\mathbb C^d)^{\otimes(r+1)}$, without a Hermiticity assumption. Define $f_P(X)=\operatorname{tr}_{1\ldots r}[P(X_1\otimes\cdots\otimes X_r\otimes I)]$. For every complex input tuple and every $v\in\mathbb C^d$,
--
--   $$\langle v,f_P(X)v\rangle=\operatorname{tr}[P(X_1\otimes\cdots\otimes X_r\otimes|v\rangle\langle v|)].$$
--
--   For a PSD tuple $X$, $f_P(X)\ge0$ if and only if the scalar on the right is real and nonnegative for every $v$. Globally,
--
--   $$[\forall X_1,\ldots,X_r\ge0,\ f_P(X)\ge0]\quad\Longleftrightarrow\quad P\text{ is Hermitian and block positive}.$$
--
--   Block positivity tests every fully separable state, equivalently every pure product vector. The global quantifier is essential to this correspondence.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 14, Eqs.(57)–(59): operator contraction and block positivity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- General construction, Eqs.57–59 (PDF pp.14–15). The last equivalence is
universal in all PSD input tuples; one positive value alone does not imply block
positivity. Complex scalar inequalities include both reality and nonnegativity. -/
theorem contraction_and_block_positivity {d r : ℕ} (hd : 0 < d) (hr : 1 ≤ r)
    (P : (Matrix (Fin (r+1) → Fin d) (Fin (r+1) → Fin d) ℂ)) :
    (∀ (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) (v : Fin d → ℂ),
      finiteMatrixElement v (contractInputs P X) v =
        Matrix.trace (P * tensorMatrices (Fin.lastCases (rankOneOperator v v) X))) ∧
    (∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), (∀ i, (X i).PosSemidef) →
      ((contractInputs P X).PosSemidef ↔ ∀ v : Fin d → ℂ,
        RealNonnegative (Matrix.trace (P * tensorMatrices (Fin.lastCases (rankOneOperator v v) X))))) ∧
    (PositiveMap (contractInputs P) ↔ FullyBlockPositive P) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
