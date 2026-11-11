-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_simplex_images
-- name    : WaitFreeTasks.Characterization.simplex_images
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:30.269299+00:00
-- url     : https://prove2.me/theorems/8c417372-ae62-4033-8f1d-d31f3d4bf1df
-- title:
--   Lemma 2 — Affine simplex images in a subdivision
-- statement:
--   Let $I,O$ be finite simplicial complexes and let $f:|I|\to|O|$ be a PL map. There exists a geometric subdivision $D$ of $I$ satisfying
--
--   $$\forall\sigma\in D,\quad f|_{|\sigma|}\text{ is affine},\qquad \exists\tau_\sigma\in O:\ f(|\sigma|)\subseteq|\tau_\sigma|.$$
--
--   Here affine means respecting every real convex barycentric combination of the vertices. This is the geometric interface used by subsequent preimage and coloring constructions. No finite-to-one hypothesis is imposed.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - generalization: the finite chromatic input and output complexes used in Section 4 → arbitrary finite simplicial complexes; reason: no coloring enters these triangulation assertions and the underlying complexes of every source task specialize to them
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 9 (PDF p. 11), Lemma 2

import Definitions.Def_WaitFreeTasks_Characterization_Complexes

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 2** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 9, PDF p. 11). For finite complexes `I`, `O` and a PL map
`f : |I| → |O|`, there is a subdivision `div(I)` of `I` such that on every simplex `σ ∈ div(I)`
the map `f` is linear (affine in barycentric coordinates) and `f(|σ|) ⊆ |τ_σ|` for some simplex
`τ_σ ∈ O`. -/
theorem simplex_images {VI VO : Type} (I : Cx VI) (O : Cx VO) (f : (VI → ℝ) → (VO → ℝ))
    (hmap : Set.MapsTo f I.real O.real) (hPL : IsPL I.real f) :
    ∃ D : GCx (VI → ℝ), IsSubdivOf D I ∧
      ∀ σ ∈ D.faces, AffineOnSimplex f σ ∧ ∃ τ ∈ O.faces, f '' gs σ ⊆ face τ := by sorry

end WaitFreeTasks.Characterization
