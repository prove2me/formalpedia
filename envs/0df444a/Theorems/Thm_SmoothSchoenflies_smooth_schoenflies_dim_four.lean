-- Prove2me | Theorems.Thm_SmoothSchoenflies_smooth_schoenflies_dim_four
-- name    : SmoothSchoenflies.smooth_schoenflies_dim_four
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:28:56.015192+00:00
-- url     : https://prove2.me/theorems/21d8c33d-be20-44b5-8e2f-4e4b1fe81192
-- title:
--   Smooth 4-dimensional Schoenflies problem
-- statement:
--   Let $S^4=\{x\in\mathbb R^5:\|x\|=1\}$ with its standard smooth structure and $D^4$ the closed unit ball in $\mathbb R^4$. Let $M\subset S^4$ be a smooth $3$-dimensional submanifold diffeomorphic to $S^3$, given as the image of a smooth embedding $f:S^3\to S^4$ (a $C^\infty$ injective immersion). By the Jordan–Brouwer separation theorem $M$ separates $S^4$ into two compact connected $4$-manifolds with common boundary $M$. The conjecture: for every $x\in S^4\setminus M$, with $C_x$ the component of $S^4\setminus M$ containing $x$,
--   $$
--   \overline{C_x}\ \text{is diffeomorphic to}\ D^4,
--   $$
--   i.e. $M$ is unknotted.
--
--   This is the only dimension in which the smooth Schoenflies problem is open; a negative answer would give an exotic smooth $D^4$ embedded in $S^4$.
--
--   **Formalization Note** 'Diffeomorphic to $D^4$' is `IsSmoothClosedBallIn 3`: the image of the closed unit ball under a $C^\infty$ map $\mathbb R^4\to S^4$ that is injective and has injective differential at every point of the closed ball (boundary included). The conclusion is required for both complementary components.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem; Problem statement (box at top of page). Original appearance: [A] Alexander, PNAS 10 (1924) 6-8.

import Mathlib
import Definitions.Def_SmoothSchoenflies_basic

open Manifold Metric

namespace SmoothSchoenflies

theorem smooth_schoenflies_dim_four (f : Sph 3 → Sph 4) (hf : IsSmoothEmbeddingSph 3 f)
    (x : Sph 4) (hx : x ∉ Set.range f) :
    IsSmoothClosedBallIn 3 (closure (connectedComponentIn (Set.range f)ᶜ x)) := by sorry

end SmoothSchoenflies
