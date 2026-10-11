-- Prove2me | Theorems.Thm_SmoothSchoenflies_generalized_schoenflies
-- name    : SmoothSchoenflies.generalized_schoenflies
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:26:48.346429+00:00
-- url     : https://prove2.me/theorems/37f72375-38c1-4680-a7a6-f6119a5a2281
-- title:
--   Generalized Schoenflies theorem (topological, smooth spheres)
-- statement:
--   Let $S^n=\{x\in\mathbb R^{n+1}:\|x\|=1\}$ be the unit sphere with its standard smooth structure and $D^{n+1}=\{x\in\mathbb R^{n+1}:\|x\|\le 1\}$ the closed unit ball. Let $f:S^n\to S^{n+1}$ be a smooth embedding and let $x\in S^{n+1}\setminus f(S^n)$. Write $C_x$ for the connected component of $S^{n+1}\setminus f(S^n)$ containing $x$. Then
--   $$
--   \overline{C_x}\ \text{is homeomorphic to}\ D^{n+1}.
--   $$
--   This is the Mazur–Brown generalized Schoenflies theorem specialised to smooth (hence locally flat) spheres. For $n=3$ it says that the smooth Schoenflies problem is only about smooth structures.
--
--   **Formalization Note** 'Homeomorphic' is `Nonempty (closedBall 0 1 ≃ₜ closure C_x)` with subspace topologies.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem; 'the Mazur-Brown theorem that an embedding of S^n in S^{n+1} bounds a manifold homeomorphic to D^{n+1}' and 'By the work of Mike Freedman, M separates S^4 into two manifolds which are homeomorphic to D^4'. Refs [MAZ] Mazur, Bull. AMS 65 (1959) 59-65; [B] Brown, Bull. AMS 66 (1960) 74-76.

import Mathlib
import Definitions.Def_SmoothSchoenflies_basic

open Manifold Metric

namespace SmoothSchoenflies

theorem generalized_schoenflies (n : ℕ) (f : Sph n → Sph (n + 1))
    (hf : IsSmoothEmbeddingSph n f) (x : Sph (n + 1)) (hx : x ∉ Set.range f) :
    IsTopClosedBallIn n (closure (connectedComponentIn (Set.range f)ᶜ x)) := by sorry

end SmoothSchoenflies
