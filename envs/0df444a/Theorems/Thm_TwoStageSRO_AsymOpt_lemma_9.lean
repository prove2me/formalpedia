-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_lemma_9
-- name    : TwoStageSRO.AsymOpt.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:41.074869+00:00
-- url     : https://prove2.me/theorems/a923d22b-24f7-4fd8-be56-ed3a34a5c268
-- title:
--   Lemma 9, p. 40 — B(ζ̂,ϵ) ∩ Ξ is translation invariant along the relative interior of a face of Ξ
-- statement:
--   Let $\Xi$ be represented with $\|g_i\|_*=1$ for every constraint, let $\Delta_\Xi$ be the radius of Definition 2, and let $F$ be a face of $\Xi$. Then for all $\hat\zeta,\bar\zeta\in\operatorname{ri}(F)$ and all $\epsilon\in[0,\min\{\Delta_\Xi(\hat\zeta),\Delta_\Xi(\bar\zeta)\}]$,
--   $$\big(B(\hat\zeta,\epsilon)\cap\Xi\big)+\bar\zeta-\hat\zeta=B(\bar\zeta,\epsilon)\cap\Xi.$$
--   Moreover, if $F$ is a minimal face of $\Xi$, this equality holds for every $\epsilon\ge0$.
--
--   Points in the relative interior of the same face see the same local shape of $\Xi$; this is how feasibility of a linear decision rule near one point is transported to another in the proof of Lemma 1.
--
--   **Formalization Note** $S+\bar\zeta-\hat\zeta$ is the translate of $S$ by $\bar\zeta-\hat\zeta$. The relative interior is Mathlib's `intrinsicInterior ℝ F` (interior within the affine span), which for convex sets in $\mathbb R^d$ agrees with the paper's definition (p. 5). The normalization $\|g_i\|_*=1$ is the appendix's standing assumption (p. 33); minimality of the representation is not imposed.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 40, Lemma 9

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 40, Lemma 9:
let `F` be a face of `Ξ`; then for all `ζ̂, ζ̄ ∈ ri(F)` and all `ε ∈ [0, min{∆_Ξ(ζ̂), ∆_Ξ(ζ̄)}]`,
`B(ζ̂, ε) ∩ Ξ + ζ̄ − ζ̂ = B(ζ̄, ε) ∩ Ξ`; moreover, if `F` is a minimal face of `Ξ`, the equality holds for
every `ε ≥ 0`.

**Formalization Note** `S + ζ̄ − ζ̂` is the translate of `S` by `ζ̄ − ζ̂`. `ri(F)` is Mathlib's
`intrinsicInterior ℝ F` (the interior of `F` in its affine span), which for convex sets in `ℝᵈ` equals
the paper's line-extension definition of the relative interior (p. 5). Faces are the nonempty sets
`{ζ ∈ Ξ : G_I ζ = g⁰_I}` (`IsFace`). The appendix's standing normalization `‖gᵢ‖_* = 1` (p. 33) is the
hypothesis `hG`; minimality of the representation is not imposed (a disclosed strengthening). -/
theorem lemma_9 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1) (F : Set (Fin d → ℝ)) (hF : IsFace M F) :
    (∀ zhat ∈ intrinsicInterior ℝ F, ∀ zbar ∈ intrinsicInterior ℝ F, ∀ ε : ℝ, 0 ≤ ε →
      (ε : EReal) ≤ min (radius M p zhat) (radius M p zbar) →
      (fun ζ => ζ + (zbar - zhat)) '' (ball p zhat ε ∩ Xi M) = ball p zbar ε ∩ Xi M) ∧
    (IsMinimalFace M F →
      ∀ zhat ∈ intrinsicInterior ℝ F, ∀ zbar ∈ intrinsicInterior ℝ F, ∀ ε : ℝ, 0 ≤ ε →
      (fun ζ => ζ + (zbar - zhat)) '' (ball p zhat ε ∩ Xi M) = ball p zbar ε ∩ Xi M) := by sorry

end TwoStageSRO.AsymOpt
