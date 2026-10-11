-- Prove2me | Theorems.Thm_SmoothSchoenflies_jordan_brouwer_separation
-- name    : SmoothSchoenflies.jordan_brouwer_separation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:26:16.391519+00:00
-- url     : https://prove2.me/theorems/d381e65f-fae6-492c-8611-1fc9848f4b52
-- title:
--   Jordan–Brouwer separation for smooth $S^n\subset S^{n+1}$
-- statement:
--   Let $S^n=\{x\in\mathbb R^{n+1}:\|x\|=1\}$ be the unit sphere with its standard smooth structure and $D^{n+1}=\{x\in\mathbb R^{n+1}:\|x\|\le 1\}$ the closed unit ball. Let $f:S^n\to S^{n+1}$ be a smooth embedding (a $C^\infty$ injective immersion) with image $M=f(S^n)$. Then $S^{n+1}\setminus M$ has exactly two connected components $U$ and $V$, and $M$ is the frontier of each:
--   $$
--   \partial U=\partial V=M.
--   $$
--   This is the separation statement the Schoenflies problem is built on: the two closures $\overline U,\overline V$ are the compact manifolds whose diffeomorphism type the problem asks about.
--
--   **Formalization Note** Components are `connectedComponentIn (Set.range f)ᶜ x`; the statement asserts two points $x,y\notin M$ with distinct components, every point of the complement lies in one of these two components, and the frontier of each component equals $M$.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem; 'By the Jordan-Brouwer separation theorem, M separates S^4 into the union of two compact connected 4-manifolds which share M as a common boundary' (stated there for n = 3; formalized for all n).

import Mathlib
import Definitions.Def_SmoothSchoenflies_basic

open Manifold Metric

namespace SmoothSchoenflies

theorem jordan_brouwer_separation (n : ℕ) (f : Sph n → Sph (n + 1))
    (hf : IsSmoothEmbeddingSph n f) :
    ∃ x y : Sph (n + 1), x ∉ Set.range f ∧ y ∉ Set.range f ∧
      connectedComponentIn (Set.range f)ᶜ x ≠ connectedComponentIn (Set.range f)ᶜ y ∧
      (∀ z ∉ Set.range f,
        connectedComponentIn (Set.range f)ᶜ z = connectedComponentIn (Set.range f)ᶜ x ∨
        connectedComponentIn (Set.range f)ᶜ z = connectedComponentIn (Set.range f)ᶜ y) ∧
      frontier (connectedComponentIn (Set.range f)ᶜ x) = Set.range f ∧
      frontier (connectedComponentIn (Set.range f)ᶜ y) = Set.range f := by sorry

end SmoothSchoenflies
