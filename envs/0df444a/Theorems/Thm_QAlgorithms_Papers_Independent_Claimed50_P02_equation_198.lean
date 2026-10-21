-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_equation_198
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.equation_198
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:37:27.596611+00:00
-- url     : https://prove2.me/theorems/d890fa05-5962-4a77-a222-cd353d71cf68
-- title:
--   Appendix A, Eq.(198): contraction with a computational matrix unit
-- statement:
--   Let $d\ge2$, $p,q\ge0$, let $\sigma$ be a walled diagram, and let $i,j\in[d]^{p+q}$ be computational basis labels. Write $\sigma_{ji}$ for the product of the equality deltas on its connected endpoints, with row label $j$ and column label $i$. Then
--   $$
--   \operatorname{Tr}\!\left(\psi^d_{p,q}(\sigma)|i\rangle\langle j|\right)=\sigma_{ji}.
--   $$
--   The reversed indices are essential. This gives the matrix-unit contraction rule used to process sparse input matrices.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 58, Appendix A, Eq.(198): contraction with a computational matrix unit

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.58, Eq.(198): the basis unit |i><j| reads the reversed (j,i)
entry of the diagram action, whose coefficient is the connectivity delta of Eq.(43). -/
theorem equation_198 {d p q : ℕ} (hd : 2 ≤ d) (pi : Diagram p q)
    (i j : (Sites (Fin d) (p+q))) :
    Matrix.trace (diagramMatrix d pi * Matrix.single i j 1) =
      relationMatrix d (traceConnectivity ∅ pi) j i := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
