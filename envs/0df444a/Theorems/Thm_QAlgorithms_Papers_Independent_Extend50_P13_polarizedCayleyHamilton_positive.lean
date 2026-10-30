-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_polarizedCayleyHamilton_positive
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.polarizedCayleyHamilton_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:32:51.15816+00:00
-- url     : https://prove2.me/theorems/466edd0b-c15b-4220-b4af-1a6ebef446fc
-- title:
--   Theorem 9: polarized Cayley–Hamilton inequality (paper headline)
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For every tuple $X_1,\ldots,X_r\ge0$,
--
--   $$f_\lambda(X_1,\ldots,X_r)\ge0.$$
--
--   No trace normalization is imposed. This is the polarized Cayley–Hamilton inequality, extending the corresponding vanishing identity to the positive cone.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 11, Theorem 9: polarized Cayley–Hamilton inequality (paper headline)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Theorem 9, Eq.38 (PDF p.11, normalization pp.9–10). Includes every partition,
also those with more rows than the physical dimension, and unnormalized PSD inputs. -/
theorem polarizedCayleyHamilton_positive {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1))
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) (hX : ∀ i, (X i).PosSemidef) :
    (polarizedMap lambda X).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
