-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_antisymmetric_three_example
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.antisymmetric_three_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:38:57.257028+00:00
-- url     : https://prove2.me/theorems/3337b586-6ead-417d-8ef7-0a4a8a1d197c
-- title:
--   Example 10: three-box antisymmetric map
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For $\lambda=(1,1,1)$,
--
--   $$f_\lambda(X,Y)=\frac16\left[(\operatorname{tr}(X)\operatorname{tr}(Y)-\operatorname{tr}(XY))I-\operatorname{tr}(X)Y-\operatorname{tr}(Y)X+XY+YX\right].$$
--
--   It vanishes for all complex $2\times2$ inputs. In every positive dimension it is positive semidefinite whenever $X,Y\ge0$. This is the normalized three-box antisymmetric example.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 11, Example 10: three-box antisymmetric map

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Example 10, Eq.40 (PDF p.11): exact 1/6 normalization, the identity in
dimension two, and positivity for all positive dimensions. -/
theorem antisymmetric_three_example
    (lambda : QAlgorithms.Schur.Partition 3 3) (hshape : lambda.val.rowLens = [1,1,1]) :
    (∀ (d : ℕ), 0 < d → ∀ X Y : (Matrix (Fin d) (Fin d) ℂ),
      polarizedMap lambda ![X,Y] = (1/6 : ℂ) • antisymmetricThree X Y) ∧
    (∀ X Y : (Matrix (Fin 2) (Fin 2) ℂ), polarizedMap lambda ![X,Y] = 0) ∧
    (∀ (d : ℕ), 0 < d → ∀ X Y : (Matrix (Fin d) (Fin d) ℂ),
      X.PosSemidef → Y.PosSemidef → (polarizedMap lambda ![X,Y]).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
