-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_real_extension_reflection_symmetry
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.real_extension_reflection_symmetry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:58:35.453194+00:00
-- url     : https://prove2.me/theorems/d524099a-9a3e-46ed-b24c-3d59fa4b0078
-- title:
--   Paper result: real extension dimensions, periodicity and reflection supersymmetry
-- statement:
--   Let $V=\mathbb R^{p,q}\ne0$, $n=p+q$, $s=p-q$, and $S$ be the full irreducible real Clifford spinor with $v^2=-g(v,v)$. Let $L^+$ and $L^-$ be the real dimensions of the equivariant symmetric and alternating bracket spaces. Their values are the complete total table below. On the parity lattice $G=\{n+s\text{ even}\}$, the extensions have period eight separately in $n,s$ and satisfy
--   $$L^\pm(-4-n,s)=L^\pm(4-n,s)=L^\pm(n,s),\quad L^\pm(n,-2-s)=L^\pm(n,6-s)=L^\pm(n,s),\quad L^+(-n,s)=L^-(n,s).$$
--   Each dimension belongs to $\{0,1,2,3,4,6\}$. These are dimensions of independent brackets, never counts of isomorphism classes.
--
--   For columns $n=-3,-2,-1,0,1,2,3,4$, the total table is
--
--   | $s$ | $-3$ | $-2$ | $-1$ | $0$ | $1$ | $2$ | $3$ | $4$ |
--   |---|---|---|---|---|---|---|---|---|
--   | $4$ | — | $(2,6)$ | — | $(4,4)$ | — | $(6,2)$ | — | $(4,4)$ |
--   | $3$ | $(1,3)$ | — | $(1,3)$ | — | $(3,1)$ | — | $(3,1)$ | — |
--   | $2$ | — | $(2,6)$ | — | $(4,4)$ | — | $(6,2)$ | — | $(4,4)$ |
--   | $1$ | $(1,3)$ | — | $(1,3)$ | — | $(3,1)$ | — | $(3,1)$ | — |
--   | $0$ | — | $(0,2)$ | — | $(1,1)$ | — | $(2,0)$ | — | $(1,1)$ |
--   | $-1$ | $(0,1)$ | — | $(0,1)$ | — | $(1,0)$ | — | $(1,0)$ | — |
--   | $-2$ | — | $(0,2)$ | — | $(1,1)$ | — | $(2,0)$ | — | $(1,1)$ |
--   | $-3$ | $(1,3)$ | — | $(1,3)$ | — | $(3,1)$ | — | $(3,1)$ | — |
--
--   Pairs are $(L^+,L^-)$; dashes mean incompatible parity. This dimension interface describes independent extension brackets.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 1, Paper result: real extension dimensions, periodicity and reflection supersymmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Abstract / introduction, PDF pp. 1,4--5: total table, period eight, all four
Gamma reflections and the n=0 supersymmetry. These are dimensions, not isomorphism counts. -/
theorem real_extension_reflection_symmetry :
    RealDimensionClassification ∧ RealTableSymmetries ∧
    (∀ n s : ℤ, Even (n + s) →
      realTotalTable (-4 - n) s = realTotalTable n s ∧
      realTotalTable (4 - n) s = realTotalTable n s ∧
      realTotalTable n (-2 - s) = realTotalTable n s ∧
      realTotalTable n (6 - s) = realTotalTable n s ∧
      (realTotalTable n s).1 ∈ ({0, 1, 2, 3, 4, 6} : Finset ℕ) ∧
      (realTotalTable n s).2 ∈ ({0, 1, 2, 3, 4, 6} : Finset ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
