-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_lemma_5
-- name    : TwoStageSRO.AsymOpt.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:25.29026+00:00
-- url     : https://prove2.me/theorems/5ea076e1-623f-4f57-9edc-dd08c04cdafb
-- title:
--   Lemma 5, p. 34 — for ϵ ≤ ∆_Ξ(ζ̂), B(ζ̂, λϵ) ∩ Ξ is the λ-homothety of B(ζ̂, ϵ) ∩ Ξ about ζ̂
-- statement:
--   Let $\Xi=\{\zeta: g_i^\top\zeta\ge g^0_i\}$ be represented with $\|g_i\|_*=1$ for every constraint, and let $\Delta_\Xi$ be the radius of Definition 2. Let $\hat\zeta\in\Xi$. Then for all $\epsilon\in(0,\Delta_\Xi(\hat\zeta)]$ and $\lambda\in(0,1]$,
--   $$B(\hat\zeta,\lambda\epsilon)\cap\Xi=\big\{\lambda\zeta+(1-\lambda)\hat\zeta:\ \zeta\in B(\hat\zeta,\epsilon)\cap\Xi\big\}.$$
--
--   Below its radius, the shape of a ball intersected with $\Xi$ around a point does not depend on the size of the ball; this scaling property is used in the proofs of Lemma 1 and of display (3).
--
--   **Formalization Note** The normalization $\|g_i\|_*=1$ is the appendix's standing assumption (p. 33) and is a hypothesis; its other standing assumption, that the representation of $\Xi$ is minimal, is not imposed. $\Delta_\Xi$ is `EReal`-valued and $\epsilon\le\Delta_\Xi(\hat\zeta)$ is compared in `EReal`.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 34, Lemma 5

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 34, Lemma 5:
let `ζ̂ ∈ Ξ`; then for all `ε ∈ (0, ∆_Ξ(ζ̂)]` and `λ ∈ (0, 1]`,
`B(ζ̂, λε) ∩ Ξ = {λζ + (1 − λ)ζ̂ : ζ ∈ B(ζ̂, ε) ∩ Ξ}`.

**Formalization Note** The appendix's standing normalization `‖gᵢ‖_* = 1` (p. 33) is the hypothesis
`hG`; its other standing assumption, minimality of the representation of `Ξ`, is not imposed (a
disclosed strengthening). `λ` is `lam`; `∆_Ξ` is `radius` (an `EReal`). -/
theorem lemma_5 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (zhat : Fin d → ℝ) (hz : zhat ∈ Xi M) (ε : ℝ) (hε : 0 < ε)
    (hεΔ : (ε : EReal) ≤ radius M p zhat) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ball p zhat (lam * ε) ∩ Xi M =
      (fun ζ => lam • ζ + (1 - lam) • zhat) '' (ball p zhat ε ∩ Xi M) := by sorry

end TwoStageSRO.AsymOpt
