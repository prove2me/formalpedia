-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_general_linear_equivariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.general_linear_equivariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:40:29.502892+00:00
-- url     : https://prove2.me/theorems/7f52b5b8-9d7e-484b-96d8-60b525fa29fb
-- title:
--   Unnumbered extension after Proposition 11: GL equivariance
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For every invertible $d\times d$ matrix $A$ and arbitrary inputs,
--
--   $$f_\lambda(AX_1A^{-1},\ldots,AX_rA^{-1})=Af_\lambda(X_1,\ldots,X_r)A^{-1}.$$
--
--   Thus the equivariance extends to the general linear group, acting by conjugation on the one-factor output.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 11, Unnumbered extension after Proposition 11: GL equivariance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Unnumbered GL extension following Proposition 11 (PDF p.11). An invertible
matrix acts by simultaneous conjugation on inputs and ordinary conjugation on the
one-factor output. -/
theorem general_linear_equivariance {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1))
    (A : ((Matrix (Fin d) (Fin d) ℂ))ˣ) (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) :
    polarizedMap lambda (fun i => (A : (Matrix (Fin d) (Fin d) ℂ))*X i*(↑(A⁻¹) : (Matrix (Fin d) (Fin d) ℂ))) =
      (A : (Matrix (Fin d) (Fin d) ℂ))*polarizedMap lambda X*(↑(A⁻¹) : (Matrix (Fin d) (Fin d) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
