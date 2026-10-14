-- Prove2me | Theorems.Thm_SliceRibbon_ribbon_isSlice
-- name    : SliceRibbon.ribbon_isSlice
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T11:54:01.140336+00:00
-- url     : https://prove2.me/theorems/bdce5593-16fe-405d-b13e-d65692280bbd
-- title:
--   Ribbon knots are slice (Fox)
-- statement:
--   Write $S^3=\{x\in\mathbb R^4:\|x\|=1\}$, $B^4=\{x\in\mathbb R^4:\|x\|\le1\}$ and $D^2=\{z\in\mathbb R^2:\|z\|\le1\}$. A *knot* is the image $K=\gamma(\mathbb R)$ of a $C^\infty$, $1$-periodic map $\gamma:\mathbb R\to S^3$ that is injective on $[0,1)$ and has nowhere-vanishing velocity. If $K$ bounds a ribbon disc in $S^3$ (an immersed disc with only ribbon singularities), then $K$ bounds a smoothly embedded disc in $B^4$ meeting $S^3$ transversally exactly in $K$:
--   $$K\ \text{ribbon}\ \Longrightarrow\ K\ \text{slice}.$$
--
--   This is the known direction of the slice–ribbon problem; the conjecture asks for its converse.
--
--   **Formalization Note** `IsRibbon γ → IsSlice γ` for every `γ` with `IsKnot γ`.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; [F] R. H. Fox, Some problems in knot theory, Topology of 3-manifolds and related topics (Proc. Univ. of Georgia Institute, 1961), 1962, pp. 168-176 (every ribbon knot is slice; the converse is asked).

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric

namespace SliceRibbon

theorem ribbon_isSlice (γ : ℝ → R4) (hγ : IsKnot γ) (hr : IsRibbon γ) :
    IsSlice γ := by sorry

end SliceRibbon
