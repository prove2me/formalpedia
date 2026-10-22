-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_real_extension_dimensions
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.real_extension_dimensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:08:28.395508+00:00
-- url     : https://prove2.me/theorems/67d074b2-878f-44c8-99c9-1759c2680bfe
-- title:
--   Theorem 6.4
-- statement:
--   Let $V=\mathbb R^{p,q}\ne0$ and let $S$ be its full irreducible real Clifford spinor. Put $n=p+q$, $s=p-q$. Let $J^{\sigma}$ consist of equivariant maps $V\to(S\otimes S)^*$ whose values are bilinear forms of exchange sign $\sigma\in\{1,-1\}$. If the even restriction splits, let $J^{\sigma\iota}$ additionally impose same-half support for $\iota=1$ or mixed-half support for $\iota=-1$. Zero belongs to every such subspace. Define $L^{\sigma}=\dim_{\mathbb R}J^{\sigma}$ and $L^{\sigma\iota}=\dim_{\mathbb R}J^{\sigma\iota}$. The actual dimensions equal every entry of the table below, and only signatures $s\equiv0,1,2,4\pmod8$ split. The dimensions depend only on $n,s$ modulo eight and satisfy
--   $$L^+(-n,s)=L^-(n,s),\qquad L^{+\iota}(-n,s)=L^{-\iota}(n,s).$$
--   Negative coordinates and residue zero denote periodic extension from positive-dimensional signatures. The refined assertions are made only for an actual semispinor splitting.
--
--   The complete real table, with columns $n=-3,-2,-1,0,1,2,3,4$ read modulo eight, is
--
--   | $s$ | $-3$ | $-2$ | $-1$ | $0$ | $1$ | $2$ | $3$ | $4$ |
--   |---|---|---|---|---|---|---|---|---|
--   | $4$ | — | $(2,0,6,0)$ | — | $(0,4,0,4)$ | — | $(6,0,2,0)$ | — | $(0,4,0,4)$ |
--   | $3$ | $(1,3)$ | — | $(1,3)$ | — | $(3,1)$ | — | $(3,1)$ | — |
--   | $2$ | — | $(0,2,4,2)$ | — | $(2,2,2,2)$ | — | $(4,2,0,2)$ | — | $(2,2,2,2)$ |
--   | $1$ | $(0,1,2,1)$ | — | $(0,1,2,1)$ | — | $(2,1,0,1)$ | — | $(2,1,0,1)$ | — |
--   | $0$ | — | $(0,0,2,0)$ | — | $(0,1,0,1)$ | — | $(2,0,0,0)$ | — | $(0,1,0,1)$ |
--   | $-1$ | $(0,1)$ | — | $(0,1)$ | — | $(1,0)$ | — | $(1,0)$ | — |
--   | $-2$ | — | $(0,2)$ | — | $(1,1)$ | — | $(2,0)$ | — | $(1,1)$ |
--   | $-3$ | $(1,3)$ | — | $(1,3)$ | — | $(3,1)$ | — | $(3,1)$ | — |
--
--   Pairs are ordered $(L^+,L^-)$ and quadruples $(L^{++},L^{+-},L^{-+},L^{--})$. Dashes are incompatible parity, not dimension-zero assertions. This identifies actual equivariant dimensions with the table data.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 38, Theorem 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Theorem 6.4, PDF p. 38. Dimensions are finranks of actual equivariant subspaces;
the integer tables are conclusions. Refined counts occur only for a genuine split. -/
theorem real_extension_dimensions : RealDimensionClassification ∧ RealTableSymmetries := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
