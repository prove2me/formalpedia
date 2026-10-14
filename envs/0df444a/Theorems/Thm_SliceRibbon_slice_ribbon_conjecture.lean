-- Prove2me | Theorems.Thm_SliceRibbon_slice_ribbon_conjecture
-- name    : SliceRibbon.slice_ribbon_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T11:57:07.920489+00:00
-- url     : https://prove2.me/theorems/48c67eea-e699-4d84-ab3e-6444ce8f0036
-- title:
--   Slice–ribbon conjecture (Fox)
-- statement:
--   Write $S^3=\{x\in\mathbb R^4:\|x\|=1\}$, $B^4=\{x\in\mathbb R^4:\|x\|\le1\}$ and $D^2=\{z\in\mathbb R^2:\|z\|\le1\}$. A *knot* is the image $K=\gamma(\mathbb R)$ of a $C^\infty$, $1$-periodic map $\gamma:\mathbb R\to S^3$ that is injective on $[0,1)$ and has nowhere-vanishing velocity. $K$ is *slice* if it bounds a smoothly embedded disc in $B^4$ which meets $S^3$ transversally exactly in its boundary $K$, and *ribbon* if it bounds an immersed disc in $S^3$ whose only singularities are ribbon singularities (arcs of transverse double points, each with one preimage arc in the interior of the disc and the other running across the disc between two boundary points; no triple points).
--
--   **Conjecture.** For every knot $K\subset S^3$,
--   $$K\ \text{slice}\ \Longrightarrow\ K\ \text{ribbon}.$$
--
--   The converse implication is classical, so the conjecture asserts that sliceness, a $4$-dimensional property, coincides with the $3$-dimensional ribbon property. It is listed as *Outstanding* in the Open Problem Garden.
--
--   **Formalization Note** Knots are `IsKnot γ`, sliceness is `IsSlice γ` and ribbon is Fox's immersed-disc definition `IsRibbon γ` from `Definitions.Def_SliceRibbon_basic`; the problem is the smooth one.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; Conjecture (box at top of page): 'Given a knot in S^3 which is slice, is it a ribbon knot?'. Original appearance: [F] R. H. Fox, Some problems in knot theory, 1962, pp. 168-176.

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric

namespace SliceRibbon

theorem slice_ribbon_conjecture (γ : ℝ → R4) (hγ : IsKnot γ) (hs : IsSlice γ) :
    IsRibbon γ := by sorry

end SliceRibbon
