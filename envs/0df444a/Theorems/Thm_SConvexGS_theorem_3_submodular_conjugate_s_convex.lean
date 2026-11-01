-- Prove2me | Theorems.Thm_SConvexGS_theorem_3_submodular_conjugate_s_convex
-- name    : SConvexGS.theorem_3_submodular_conjugate_s_convex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:31.106281+00:00
-- url     : https://prove2.me/theorems/0682ffc2-c48d-4d95-aa03-4ad804df8f0c
-- title:
--   Theorem 3 — a lsc, $C^1$, strictly convex $f$ with open domain and submodular $f^*$ is S-convex
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be a lower semicontinuous, continuously differentiable, strictly convex function with an open $\operatorname{dom}(f)$. If its convex conjugate $f^*$ is submodular, then $f$ is S-convex.
--
--   This is the converse of Theorem 2 under mild regularity conditions. Applied to $-f$, it turns the supermodularity of $f_*$ into the S-concavity of $f$.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → (−∞, ∞] → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊥; reason: Lean convention; same functions, with ⊤ for +∞
--   - encoding: continuously differentiable, strictly convex or concave f → ContDiffOn and StrictConvexOn or StrictConcaveOn of toReal ∘ f on dom f; reason: these notions apply to the finite part of f, on the open set dom f; toReal of ±∞ is 0, so the set cannot be univ
--   - encoding: the conjugate, defined on p.14 for dom f ≠ ∅ → at dom f = ∅ the def is ⊥ and the conclusion holds; reason: no hypothesis is needed for this undefined case
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Theorem 3, p.14

import Mathlib
import Definitions.Def_SConvexGS_convexConj
import Definitions.Def_SConvexGS_IsSubmodular
import Definitions.Def_SConvexGS_IsSConvex

namespace SConvexGS

/-- **Theorem 3** (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), p.14): let
`f : ℝⁿ → (−∞, ∞]` be a lsc, continuously differentiable, strictly convex function with an open
`dom(f)`. If `f*` is submodular, then `f` is S-convex.

Formalization Note: differentiability and strict convexity are on `dom f`, of `toReal ∘ f`. At
`dom f = ∅` the conjugate `def` is `⊥` and the conclusion holds vacuously. -/
theorem theorem_3_submodular_conjugate_s_convex {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_bot : ∀ x, f x ≠ ⊥) (hf_lsc : LowerSemicontinuous f) (hf_open : IsOpen (dom f))
    (hf_C1 : ContDiffOn ℝ 1 (fun x => (f x).toReal) (dom f))
    (hf_strict : StrictConvexOn ℝ (dom f) (fun x => (f x).toReal))
    (hf_sub : IsSubmodular (convexConj f)) :
    IsSConvex f := by sorry

end SConvexGS
