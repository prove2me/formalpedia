-- Prove2me | Theorems.Thm_SmoothSchoenflies_smooth_schoenflies_dim_three
-- name    : SmoothSchoenflies.smooth_schoenflies_dim_three
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:27:57.278767+00:00
-- url     : https://prove2.me/theorems/12e14322-198e-408e-a0f9-f0c2d86d83b2
-- title:
--   Smooth Schoenflies theorem for $S^2\subset S^3$ (Alexander)
-- statement:
--   Let $S^n=\{x\in\mathbb R^{n+1}:\|x\|=1\}$ be the unit sphere with its standard smooth structure and $D^{n+1}=\{x\in\mathbb R^{n+1}:\|x\|\le 1\}$ the closed unit ball. Let $f:S^2\to S^3$ be a smooth embedding and $x\in S^3\setminus f(S^2)$, with $C_x$ the component of $S^3\setminus f(S^2)$ containing $x$. Then
--   $$
--   \overline{C_x}\ \text{is diffeomorphic to}\ D^3.
--   $$
--   This is Alexander's theorem, the case $n=2$ of the statement that every smooth $S^n\subset S^{n+1}$ is unknotted.
--
--   **Formalization Note** 'Diffeomorphic to $D^3$' is `IsSmoothClosedBallIn 2`.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem; 'For n = 2 it's due to Alexander (see Hatcher's 3-manifolds notes for a modern exposition).' Ref [A] Alexander, PNAS 10 (1924) 6-8.

import Mathlib
import Definitions.Def_SmoothSchoenflies_basic

open Manifold Metric

namespace SmoothSchoenflies

theorem smooth_schoenflies_dim_three (f : Sph 2 → Sph 3) (hf : IsSmoothEmbeddingSph 2 f)
    (x : Sph 3) (hx : x ∉ Set.range f) :
    IsSmoothClosedBallIn 2 (closure (connectedComponentIn (Set.range f)ᶜ x)) := by sorry

end SmoothSchoenflies
