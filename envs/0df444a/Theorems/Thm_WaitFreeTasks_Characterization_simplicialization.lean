-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_simplicialization
-- name    : WaitFreeTasks.Characterization.simplicialization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:33.436017+00:00
-- url     : https://prove2.me/theorems/03b4cc56-18e0-4b4f-b818-02902108cb3b
-- title:
--   Lemma 1 — Simplicial approximation for PL maps
-- statement:
--   Let $I,O$ be finite simplicial complexes and let $f:|I|\to|O|$ be PL in the local conical sense of Section 2.2. There are geometric subdivisions $D$ of $I$ and $E$ of $O$, and a simplicial vertex map $\phi:D\to E$, such that
--
--   $$f\!\left(\sum_{v\in\sigma} a_vv\right)=\sum_{v\in\sigma} a_v\phi(v)\quad(\sigma\in D,\ a_v\ge0,\ \sum a_v=1).$$
--
--   Thus $\phi$ induces the given map exactly, throughout the real realizations. This supplies simultaneous triangulations for the PL development; finite fibers and chromaticity are not hypotheses.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - generalization: the finite chromatic input and output complexes used in Section 4 → arbitrary finite simplicial complexes; reason: no coloring enters these triangulation assertions and the underlying complexes of every source task specialize to them
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 9 (PDF p. 11), Lemma 1

import Definitions.Def_WaitFreeTasks_Characterization_Complexes

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 1** (Simplicial approximation for PL maps [RS82, Theorem 2.14]; Attiya–Paz, STOC 2027 submission #828 (October 2026), printed
p. 9, PDF p. 11). For finite complexes `I`, `O` and a PL map `f : |I| → |O|`, there are
subdivisions `div(I)` of `I` and `div(O)` of `O` and a simplicial map `φ : div(I) → div(O)` that
induces `f`: on every simplex of `div(I)`, `f` is the affine extension of `φ` on its vertices. -/
theorem simplicialization {VI VO : Type} (I : Cx VI) (O : Cx VO) (f : (VI → ℝ) → (VO → ℝ))
    (hmap : Set.MapsTo f I.real O.real) (hPL : IsPL I.real f) :
    ∃ (D : GCx (VI → ℝ)) (D' : GCx (VO → ℝ)) (φ : (VI → ℝ) → (VO → ℝ)),
      IsSubdivOf D I ∧ IsSubdivOf D' O ∧ (∀ σ ∈ D.faces, σ.image φ ∈ D'.faces) ∧
      ∀ σ ∈ D.faces, ∀ a : (VI → ℝ) → ℝ, (∀ v ∈ σ, 0 ≤ a v) → ∑ v ∈ σ, a v = 1 →
        f (∑ v ∈ σ, a v • v) = ∑ v ∈ σ, a v • φ v := by sorry

end WaitFreeTasks.Characterization
