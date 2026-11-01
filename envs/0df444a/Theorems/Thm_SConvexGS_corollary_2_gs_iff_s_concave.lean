-- Prove2me | Theorems.Thm_SConvexGS_corollary_2_gs_iff_s_concave
-- name    : SConvexGS.corollary_2_gs_iff_s_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:01.180078+00:00
-- url     : https://prove2.me/theorems/928a60fc-f8c2-41e4-93d0-5af45f0d8d79
-- title:
--   Corollary 2 — a usc, coercive, $C^1$, strictly concave $f$ with open domain is a proper GS-function iff it is S-concave
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be an upper semicontinuous, coercive, continuously differentiable, strictly concave function with an open $\operatorname{dom}(f)$. Then
--
--   $$f\text{ is a proper GS-function}\iff f\text{ is S-concave}.$$
--
--   Through the quasilinear reading of Definition 3, the corollary characterizes gross substitutability in divisible markets on the utility function itself.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - encoding: lim_{‖x‖₂→+∞} f(x)/‖x‖₂ = −∞ → IsCoercive f: ∀ M, ∃ R, ‖x‖₂ ≥ R → f x ≤ M‖x‖₂; reason: equivalent to the limit, without a division in EReal
--   - encoding: continuously differentiable, strictly convex or concave f → ContDiffOn and StrictConvexOn or StrictConcaveOn of toReal ∘ f on dom f; reason: these notions apply to the finite part of f, on the open set dom f; toReal of ±∞ is 0, so the set cannot be univ
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Corollary 2, p.23

import Mathlib
import Definitions.Def_SConvexGS_IsCoercive
import Definitions.Def_SConvexGS_IsProperGS
import Definitions.Def_SConvexGS_IsSConcave

namespace SConvexGS

/-- **Corollary 2** (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), p.23): let
`f : ℝⁿ → [−∞, ∞)` be a usc, coercive, continuously differentiable, strictly concave function with
an open `dom(f)`. Then `f` is a proper GS-function if and only if it is S-concave.

Formalization Note: differentiability and strict concavity are on `dom f`, of `toReal ∘ f`. There
is no `(dom f).Nonempty`: at `f ≡ ⊥` both sides hold (`argMaxTilt` has no domain clause). -/
theorem corollary_2_gs_iff_s_concave {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_coercive : IsCoercive f)
    (hf_open : IsOpen (dom f))
    (hf_C1 : ContDiffOn ℝ 1 (fun x => (f x).toReal) (dom f))
    (hf_strict : StrictConcaveOn ℝ (dom f) (fun x => (f x).toReal)) :
    IsProperGS f ↔ IsSConcave f := by sorry

end SConvexGS
