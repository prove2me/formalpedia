-- Prove2me | Theorems.Thm_SliceRibbon_round_unknot_isRibbon
-- name    : SliceRibbon.round_unknot_isRibbon
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T11:56:38.714414+00:00
-- url     : https://prove2.me/theorems/e12b0574-5960-42a2-89d0-2cc03654d5d2
-- title:
--   The round unknot is a ribbon knot
-- statement:
--   Let $\gamma(t)=(\cos 2\pi t,\sin 2\pi t,0,0)\in S^3\subset\mathbb R^4$. Then $\gamma$ parametrises a knot (it is $C^\infty$, $1$-periodic, injective on $[0,1)$, with nonzero velocity) and
--   $$\gamma(\mathbb R)\ \text{is a ribbon knot},$$
--   i.e. it bounds an immersed disc in $S^3$ with only ribbon singularities (here an embedded disc suffices).
--
--   This sanity check shows that the definitions of knots and ribbon discs used in this mission are satisfiable.
--
--   **Formalization Note** `IsKnot γ ∧ IsRibbon γ` for the explicit $\gamma$, written with `!₂[...]`.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; sanity check of the definitions (the unknot is ribbon).

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric

namespace SliceRibbon

theorem round_unknot_isRibbon :
    IsKnot (fun t : ℝ => !₂[Real.cos (2 * π * t), Real.sin (2 * π * t), 0, 0]) ∧
      IsRibbon (fun t : ℝ => !₂[Real.cos (2 * π * t), Real.sin (2 * π * t), 0, 0]) := by sorry

end SliceRibbon
