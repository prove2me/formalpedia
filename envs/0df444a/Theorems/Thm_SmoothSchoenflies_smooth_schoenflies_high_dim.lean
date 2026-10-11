-- Prove2me | Theorems.Thm_SmoothSchoenflies_smooth_schoenflies_high_dim
-- name    : SmoothSchoenflies.smooth_schoenflies_high_dim
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:28:29.015413+00:00
-- url     : https://prove2.me/theorems/7a0e7029-2c22-46a3-a03a-84bf69e6b3ab
-- title:
--   Smooth Schoenflies theorem for $S^n\subset S^{n+1}$, $n\ge 4$
-- statement:
--   Let $S^n=\{x\in\mathbb R^{n+1}:\|x\|=1\}$ be the unit sphere with its standard smooth structure and $D^{n+1}=\{x\in\mathbb R^{n+1}:\|x\|\le 1\}$ the closed unit ball. Let $n\ge 4$, let $f:S^n\to S^{n+1}$ be a smooth embedding and $x\in S^{n+1}\setminus f(S^n)$, with $C_x$ the component of $S^{n+1}\setminus f(S^n)$ containing $x$. Then
--   $$
--   \overline{C_x}\ \text{is diffeomorphic to}\ D^{n+1}.
--   $$
--   Together with the cases $n=1,2$ this leaves $n=3$ as the only open dimension.
--
--   **Formalization Note** 'Diffeomorphic to $D^{n+1}$' is `IsSmoothClosedBallIn n`.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem; 'For n ≥ 4 the result follows from the combination of the Mazur-Brown theorem that an embedding of S^n in S^{n+1} bounds a manifold homeomorphic to D^{n+1}, plus a consequence of the H-cobordism theorem which states that D^{n+1} has no exotic smooth structures which restrict to the standard smooth structure on the boundary, provided n ≥ 4.'

import Mathlib
import Definitions.Def_SmoothSchoenflies_basic

open Manifold Metric

namespace SmoothSchoenflies

theorem smooth_schoenflies_high_dim (n : ℕ) (hn : 4 ≤ n) (f : Sph n → Sph (n + 1))
    (hf : IsSmoothEmbeddingSph n f) (x : Sph (n + 1)) (hx : x ∉ Set.range f) :
    IsSmoothClosedBallIn n (closure (connectedComponentIn (Set.range f)ᶜ x)) := by sorry

end SmoothSchoenflies
