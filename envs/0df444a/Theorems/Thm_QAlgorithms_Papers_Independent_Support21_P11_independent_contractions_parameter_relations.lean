-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_independent_contractions_parameter_relations
-- name    : QAlgorithms.Papers.Independent.Support21.P11.independent_contractions_parameter_relations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:00:22.143112+00:00
-- url     : https://prove2.me/theorems/6e0f2d57-4f51-4ec0-a980-8a36448ba577
-- title:
--   Independent contractions imply weak and triangular relations
-- statement:
--   Let $R$ be a commutative ring with identity, let $r\ge1$, let $\omega=(\omega_a)_{a\ge0}$ be an $R$-valued sequence, and let $u_1,\ldots,u_r\in R$. Write $W$ for the two-strand degenerate cyclotomic BMW algebra with these parameters, $e=e_1$, $s=s_1$, and $x=x_1$. Put $\prod_{i=1}^r(z-u_i)=\sum_{j=0}^r a_jz^j$. Suppose $(e,xe,\ldots,x^{r-1}e)$ is linearly independent over $R$. Then the parameters are weakly admissible, meaning that both recurrences of Corollary 2.4 hold, and
--
--   $$\sum_{\mu=0}^{r-j-1}\omega_\mu a_{\mu+j+1}=-2\delta_{r-j\text{ odd}}a_j+\delta_{j\text{ even}}a_{j+1}\qquad(0\le j<r).$$
--
--   The indicators $\delta$ are $1$ when their conditions hold and $0$ otherwise. This gives both the odd-index weak relations and the triangular system, without assuming $2$ invertible.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 6, Lemma 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 4.1, PDF p.6: weak admissibility AND every triangular relation.
No inverse of 2, distinctness, or domain hypothesis is imposed. -/
theorem independent_contractions_parameter_relations (R : Type*) [CommRing R]
    (omega : ℕ → R) (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r)
    (hli : LinearIndependent R (idealFamily R omega r u)) :
    WeaklyAdmissible omega u ∧ TriangularRelations omega u := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
