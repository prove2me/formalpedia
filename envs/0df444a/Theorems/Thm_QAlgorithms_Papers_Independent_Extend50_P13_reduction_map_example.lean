-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_reduction_map_example
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.reduction_map_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:38:13.982133+00:00
-- url     : https://prove2.me/theorems/4ea7aab0-4ece-4d03-b846-cd55630e4a56
-- title:
--   Example 8: the rescaled reduction map
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For $\lambda=(1,1)$ and arbitrary $X$,
--
--   $$f_{(1,1)}(X)=\frac12\bigl(\operatorname{tr}(X)I-X\bigr).$$
--
--   In dimension $d=1$ both this map and the unscaled reduction map $R(X)=\operatorname{tr}(X)I-X$ vanish for every complex input. The factor two is the scaling explicitly mentioned in Example 8.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 10, Example 8: the rescaled reduction map

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Example 8 (PDF p.10). The source explicitly rescales: the normalized map is
one half of the displayed reduction polynomial. Vanishing in dimension one holds
for every complex input. -/
theorem reduction_map_example
    (lambda : QAlgorithms.Schur.Partition 2 2) (hshape : lambda.val.rowLens = [1,1]) :
    (∀ (d : ℕ), 0 < d → ∀ X : (Matrix (Fin d) (Fin d) ℂ),
      polarizedMap lambda (fun _ : Fin 1 => X) = (1/2 : ℂ) • reductionPolynomial X) ∧
    (∀ X : (Matrix (Fin 1) (Fin 1) ℂ), reductionPolynomial X = 0 ∧
      polarizedMap lambda (fun _ : Fin 1 => X) = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
