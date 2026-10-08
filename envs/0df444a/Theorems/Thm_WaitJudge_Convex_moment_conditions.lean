-- Prove2me | Theorems.Thm_WaitJudge_Convex_moment_conditions
-- name    : WaitJudge.Convex.moment_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:07:20.35007+00:00
-- url     : https://prove2.me/theorems/a6689c67-5bb3-40f0-aa46-87ef1824f797
-- title:
--   (18), Sect. 5.1.2, p. 15 — moment conditions Σ_{k≤min{m,d}} C(m,k) ∫_[0,1] (1−v)^(m−k) dF_k(v) = 1
-- statement:
--   Consider a convex scenario problem: $\mathcal X$, every $\mathcal X_\delta$ and the tie-break functions are convex, $\mathbb P$ is a probability measure, and Assumptions 1 and 2 and the measurability conditions hold. Then the generalized distribution functions $F_0,\dots,F_d$ of (12) satisfy, for every $m=0,1,2,\dots$,
--   $$\sum_{k=0}^{\min\{m,d\}}\binom mk\int_{[0,1]}(1-v)^{m-k}\,\mathrm dF_k(v)=1.$$
--
--   These infinitely many moment equations are necessary conditions on the $(d+1)$-tuples $(F_0,\dots,F_d)$ that can arise from a convex scenario problem. They are the constraints of the generalized moment problem (19) whose value bounds $\mathbb P^N\{V(x^*_N)>\epsilon(s^*_N)\}$.
--
--   **Formalization Note** $F_k$ is a finite measure on $\mathbb R$ and the integral is over the closed interval $[0,1]$. The identity is stated for every $m$, with no relation between $m$ and $d$ assumed.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 15, Sect. 5.1.2, (18)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem moment_conditions {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j))
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb) :
    ∀ m : ℕ, ∑ k ∈ Finset.range (min m d + 1),
      (m.choose k : ℝ) * ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(Fk P c X Xδ tb k) = 1 := by sorry

end WaitJudge.Convex
