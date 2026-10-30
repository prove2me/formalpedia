-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_matrix_elements_full_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.matrix_elements_full_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:36:34.189694+00:00
-- url     : https://prove2.me/theorems/fabd1a92-3e2c-47eb-a6dc-cf5f064a202a
-- title:
--   Lemma 5: matrix elements and a full trace
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For arbitrary vectors $v,w\in\mathbb C^d$ and arbitrary input matrices,
--
--   $$\langle w,f_\lambda(X_1,\ldots,X_r)v\rangle=\operatorname{tr}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes|v\rangle\langle w|)].$$
--
--   Neither vector is required to have unit norm; the bra is conjugate linear. This relates output matrix elements to full tensor traces.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 10, Lemma 5: matrix elements and a full trace

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Lemma 5, Eq.33 (PDF p.10). v and w are arbitrary vectors, not states. -/
theorem matrix_elements_full_trace {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1))
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) (v w : Fin d → ℂ) :
    finiteMatrixElement w (polarizedMap lambda X) v =
      Matrix.trace (centralProjector d lambda * tensorMatrices (Fin.lastCases (rankOneOperator v w) X)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
