-- Prove2me | Theorems.Thm_SmoothSchoenflies_smooth_schoenflies_dim_two
-- name    : SmoothSchoenflies.smooth_schoenflies_dim_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:27:30.474243+00:00
-- url     : https://prove2.me/theorems/5c47fad9-49ac-4197-9c99-2a6ef3a8f8f9
-- title:
--   Smooth Schoenflies theorem for $S^1\subset S^2$
-- statement:
--   Let $S^n=\{x\in\mathbb R^{n+1}:\|x\|=1\}$ be the unit sphere with its standard smooth structure and $D^{n+1}=\{x\in\mathbb R^{n+1}:\|x\|\le 1\}$ the closed unit ball. Let $f:S^1\to S^2$ be a smooth embedding and $x\in S^2\setminus f(S^1)$, with $C_x$ the component of $S^2\setminus f(S^1)$ containing $x$. Then
--   $$
--   \overline{C_x}\ \text{is diffeomorphic to}\ D^2.
--   $$
--   This is the case $n=1$ of the statement that every smooth $S^n\subset S^{n+1}$ is unknotted.
--
--   **Formalization Note** 'Diffeomorphic to $D^2$' is `IsSmoothClosedBallIn 1`: the image of the closed unit disc under a $C^\infty$ map $\mathbb R^2\to S^2$ injective with injective differential on the disc.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem; 'all embeddings of S^n in S^{n+1} are unknotted (bound manifolds diffeomorphic to D^{n+1}) provided n ≠ 3. For n = 1 this is due to Schoenflies.'

import Mathlib
import Definitions.Def_SmoothSchoenflies_basic

open Manifold Metric

namespace SmoothSchoenflies

theorem smooth_schoenflies_dim_two (f : Sph 1 → Sph 2) (hf : IsSmoothEmbeddingSph 1 f)
    (x : Sph 2) (hx : x ∉ Set.range f) :
    IsSmoothClosedBallIn 1 (closure (connectedComponentIn (Set.range f)ᶜ x)) := by sorry

end SmoothSchoenflies
