-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_unitary_equivariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.unitary_equivariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:39:49.555287+00:00
-- url     : https://prove2.me/theorems/6ec95b37-d04c-41d0-a782-1c65db3f291a
-- title:
--   Proposition 11: unitary equivariance
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For every unitary $U$ and arbitrary complex inputs,
--
--   $$f_\lambda(UX_1U^{-1},\ldots,UX_rU^{-1})=Uf_\lambda(X_1,\ldots,X_r)U^{-1}.$$
--
--   The inputs need not be Hermitian, as footnote 61 on PDF p.28 explicitly confirms. The result expresses equivariance under simultaneous unitary conjugation.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 11, Proposition 11: unitary equivariance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Proposition 11, Eq.41 (PDF p.11; footnote 61 p.28). No Hermiticity restriction
on the matrix variables is present. -/
theorem unitary_equivariance {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1)) :
    ConjugationEquivariant (polarizedMap (d := d) lambda) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
