-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_lemma_A_2
-- name    : RegMT.Classif.Supplement.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:30:01.593343+00:00
-- url     : https://prove2.me/theorems/bc8e8d20-36bb-4753-8b2d-95b659606f1c
-- title:
--   Lemma A.2 — support duality
-- statement:
--   Let $Z$ be a closed convex set (possibly empty, in which case both sides are $-\infty$) in a finite-dimensional real vector space with an arbitrary norm. Let $\beta$ be a continuous linear functional, $a\in\mathbb R$, $\gamma\ge0$, and let $\hat z$ be any center. Then
--   $$\sup_{z\in Z}\{a\beta(z)-\gamma\|z-\hat z\|\}=\inf_{\|p\|_*\le\gamma}\{S_Z(a\beta-p)+p(\hat z)\}.$$
--   Both sides are extended-real values; the support may be unbounded and the center need not lie in it. This supplies the support-function constraints in both piecewise-affine reformulations.
--
--   Differences from the source:
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 29, Lemma A.2; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Support

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem lemma_A_2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Z : Set V) (hclosed : IsClosed Z) (hconvex : Convex ℝ Z)
    (a γ : ℝ) (hγ : 0 ≤ γ) (β : V →L[ℝ] ℝ) (center : V) :
    (⨆ z ∈ Z, ((a * β z - γ * ‖z - center‖ : ℝ) : EReal)) =
      ⨅ p : V →L[ℝ] ℝ, ⨅ (_ : ‖p‖ ≤ γ),
        support Z (a • β - p) + (p center : EReal) := by sorry

end RegMT.Classif.Supplement
