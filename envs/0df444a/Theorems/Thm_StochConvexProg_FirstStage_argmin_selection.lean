-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_argmin_selection
-- name    : StochConvexProg.FirstStage.argmin_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:16.341974+00:00
-- url     : https://prove2.me/theorems/e62c1078-de5d-4591-8d73-71c65413f506
-- title:
--   Proof of Theorem 2, p. 188 — with C₂ bounded, the argmin multifunction is nonempty compact, measurable, with a measurable selection
-- statement:
--   Suppose $C_2$ is bounded and fix $x_1\in\mathbb R^{n_1}$. Let $S'=\{s\in S\mid \exists x_2,\ F_2(s,x_1,x_2,0)<+\infty\}$ and, for $s\in S'$, let $\Gamma(s)$ be the set of $x_2\in\mathbb R^{n_2}$ at which the infimum $q(s,x_1)$ of $F_2(s,x_1,\cdot,0)$ is attained ($\Gamma(s)=\emptyset$ for $s\notin S'$). Then:
--
--   1. for every $s\in S'$, $\Gamma(s)$ is a nonempty compact subset of $C_2$;
--   2. $\Gamma$ is a measurable multifunction;
--   3. there is a measurable $x_2:S\to\mathbb R^{n_2}$ with $x_2(s)\in\Gamma(s)$ for every $s\in S'$.
--
--   This produces the optimal recourse function whose existence is the attainment claim of Theorem 2.
--
--   **Formalization Note** This $\Gamma$ is the argmin multifunction of the proof of Theorem 2, not the feasible-recourse set (3.10); in Lean it is `argminSet`. Measurability of a multifunction is the published `DupacovaWets.Consistency.IsMeasurableMultifunction`.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 188, proof of Theorem 2, first paragraph

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage
import Definitions.Def_DupacovaWets_Consistency_Multifunction

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Proof of Theorem 2, p. 188: if `C₂` is bounded, then for each `x₁` the argmin multifunction
`Γ(s)` of `F₂(s, x₁, ·, 0)` is nonempty, compact and inside `C₂` for `s ∈ S′`, is measurable, and has a
measurable selection on `S′`. -/
theorem argmin_selection {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (hC₂ : Bornology.IsBounded pr.C₂) (x₁ : Fin n₁ → ℝ) :
    (∀ s, (∃ x₂, pr.F₂ s x₁ x₂ 0 < ⊤) →
        (pr.argminSet x₁ s).Nonempty ∧ IsCompact (pr.argminSet x₁ s) ∧
          pr.argminSet x₁ s ⊆ pr.C₂) ∧
      DupacovaWets.Consistency.IsMeasurableMultifunction (fun s => pr.argminSet x₁ s) ∧
      ∃ x₂ : S → (Fin n₂ → ℝ), Measurable x₂ ∧
        ∀ s, (∃ z, pr.F₂ s x₁ z 0 < ⊤) → x₂ s ∈ pr.argminSet x₁ s := by sorry

end StochConvexProg.FirstStage
