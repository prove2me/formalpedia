-- Prove2me | Theorems.Thm_SConvexGS_theorem_6_s_concave_is_gs
-- name    : SConvexGS.theorem_6_s_concave_is_gs
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:19.740876+00:00
-- url     : https://prove2.me/theorems/56b0b553-50b0-446f-aa9c-b8be8fab7ae5
-- title:
--   Theorem 6 — a usc, coercive S-concave function, or a usc S-concave function with bounded domain, is a GS-function
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be an upper semicontinuous S-concave function. If $f$ is coercive, then $f$ is a GS-function. In particular, $f$ is a GS-function if $\operatorname{dom}(f)$ is bounded.
--
--   This is the direction from S-concavity to GS. It yields the implication from right to left in Corollary 2, together with the existence of maximizers.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - encoding: lim_{‖x‖₂→+∞} f(x)/‖x‖₂ = −∞ → IsCoercive f: ∀ M, ∃ R, ‖x‖₂ ≥ R → f x ≤ M‖x‖₂; reason: equivalent to the limit, without a division in EReal
--   - encoding: two sentences, coercive and bounded dom(f) → one hypothesis, IsCoercive f ∨ Bornology.IsBounded (dom f); reason: the same two statements
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Theorem 6, p.22

import Mathlib
import Definitions.Def_SConvexGS_IsSConcave
import Definitions.Def_SConvexGS_IsCoercive
import Definitions.Def_SConvexGS_IsGS

namespace SConvexGS

/-- **Theorem 6** (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), p.22):
if `f : ℝⁿ → [−∞, ∞)` is a usc, coercive S-concave function, then `f` is a GS-function. In
particular, `f` is a GS-function if `f` is a usc S-concave function with a bounded `dom(f)`.

Formalization Note: the two sentences are the two sides of the disjunction. The conclusion is GS,
not proper GS. `hf_top` is the printed codomain. -/
theorem theorem_6_s_concave_is_gs {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_sconcave : IsSConcave f)
    (hf : IsCoercive f ∨ Bornology.IsBounded (dom f)) :
    IsGS f := by sorry

end SConvexGS
