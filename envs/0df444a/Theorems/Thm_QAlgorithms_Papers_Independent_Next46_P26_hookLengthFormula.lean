-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_hookLengthFormula
-- name    : QAlgorithms.Papers.Independent.Next46.P26.hookLengthFormula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:06:11.503689+00:00
-- url     : https://prove2.me/theorems/4981ef5f-6891-40d5-b93c-8eed1d9a3d0e
-- title:
--   The hook length formula for standard tableaux
-- statement:
--   Let $\lambda$ be a finite Young diagram with $n$ cells, and let $\operatorname{SYT}(\lambda)$ be all bijective fillings of its cells by $1,\ldots,n$ that increase strictly along rows and columns. For an occupied cell $z$, let $h_z$ be the number of cells in its hook, including $z$. Then
--   $$
--   |\operatorname{SYT}(\lambda)|=\frac{n!}{\prod_{z\in[\lambda]}h_z}.
--   $$
--   The empty shape has one empty tableau, $0!=1$, and empty hook product one. This counts all standard tableaux without any dimension restriction.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 4, HLF, §2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- HLF, the tableau counting equality proved in §2, pp.4–6; includes the
unique empty tableau, 0!=1 and the empty product 1. -/
theorem hookLengthFormula (lam : YoungDiagram) :
    (tableauCount lam : ℚ) = (lam.card.factorial : ℚ) / hookProduct lam := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
