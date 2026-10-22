-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_eq_3
-- name    : TwoStageSRO.AsymOpt.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:01.878636+00:00
-- url     : https://prove2.me/theorems/78028ac5-6909-44a4-8835-282c86865769
-- title:
--   Display (3), p. 16 — one ϵ > 0 such that each B(ζ̂,ϵ) ∩ Ξ, ζ̂ ∈ Ξ*, lies in a λ-homothety of some B(ζ̄,ϵ̄) ∩ Ξ, ζ̄ ∈ Ξ*
-- statement:
--   Under [A2]–[A3], fix an optimal first-stage decision $x^*$ and let $\Xi^*=\{\zeta\in\Xi:\exists y,\ Tx^*+Wy\ge h(\zeta)\}$. Let $\lambda\in(0,1)$ and $\bar\epsilon>0$. There is a radius $\epsilon>0$, depending only on $\lambda$, $\bar\epsilon$, $\Xi$ and $\Xi^*$, such that for every $\hat\zeta\in\Xi^*$ there is a realization $\bar\zeta\in\Xi^*$ with
--   $$B(\hat\zeta,\epsilon)\cap\Xi\subseteq\big\{\lambda\zeta+(1-\lambda)\bar\zeta:\ \zeta\in B(\bar\zeta,\bar\epsilon)\cap\Xi\big\}.$$
--
--   This uniform shrinkage property is the geometric input of Lemma 2; the paper derives it from Theorem 3 (Appendix C) applied to the polyhedron $\Xi^*\subseteq\Xi$.
--
--   **Formalization Note** The printed set-builder omits its bound variable; it is read as $\zeta\in B(\bar\zeta,\bar\epsilon)\cap\Xi$, as in Theorem 3 (p. 48). "Depending only on $\lambda,\bar\epsilon,\Xi,\Xi^*$" is the quantifier order: one $\epsilon$ for all $\hat\zeta$. The law is supported on $\Xi$, and [A2]–[A3] and optimality of $x^*$ are the standing assumptions of §4.2.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 16, Proof of Lemma 2, display (3)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 16, display (3)
in the proof of Lemma 2: for `λ ∈ (0, 1)` and `ε̄ > 0` there is a radius `ε > 0` (depending only on
`λ, ε̄, Ξ, Ξ*`) such that every `ζ̂ ∈ Ξ*` has some `ζ̄ ∈ Ξ*` with
`B(ζ̂, ε) ∩ Ξ ⊆ {λζ + (1 − λ)ζ̄ : ζ ∈ B(ζ̄, ε̄) ∩ Ξ}`.

**Formalization Note** The printed set-builder omits its bound variable; it is read as
`ζ ∈ B(ζ̄, ε̄) ∩ Ξ`, as in Theorem 3 (p. 48). "Depending only on `λ, ε̄, Ξ, Ξ*`" is the order
`∃ ε, ∀ ζ̂`. The §4.2 standing assumptions [A2]–[A3] and optimality of `xs = x*` are explicit. -/
theorem eq_3 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsupp : μ (Xi M)ᶜ = 0)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (εbar : ℝ) (hεbar : 0 < εbar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ zhat ∈ XiStar M xs, ∃ zbar ∈ XiStar M xs,
      ball p zhat ε ∩ Xi M ⊆
        (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by sorry

end TwoStageSRO.AsymOpt
