-- Prove2me | Theorems.Thm_SolutionQuality_SRP_prop1_ii
-- name    : SolutionQuality.SRP.prop1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:17.91239+00:00
-- url     : https://prove2.me/theorems/14f1b9b2-c77b-47fd-a565-2893d29ffd31
-- title:
--   Proposition 1 (ii), p. 6 — all limit points of {x*_n} lie in X*, w.p.1
-- statement:
--   Assume (A1)–(A3), and let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. as $\tilde\xi$. Let $x_n^*$ be an optimal solution of (SP$_n$) built on $\tilde\xi^1,\dots,\tilde\xi^n$, for each $n$, and let $X^*$ be the set of optimal solutions of (SP). Then, with probability one, every limit point (cluster point) of the sequence $\{x_n^*\}$ belongs to $X^*$:
--   $$
--   P\Big(\text{every cluster point of } (x_n^*)_{n\ge1} \text{ lies in } X^*\Big)=1.
--   $$
--
--   When (SP) has several optimal solutions the sequence $x_n^*$ need not converge, but it accumulates only at optimal solutions. This is part (ii) of Proposition 1 and is used in part (iii).
--
--   **Formalization Note.** $\hat x$ is not used and is dropped. Each $x_n^*$ is a measurable map that, almost surely, lies in $X$ and minimizes the sample mean $\bar f_n$ over $X$ on the same first $n$ observations. A limit point is a `MapClusterPt` of the sequence along `atTop`.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), p. 6, Proposition 1 (ii)

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

theorem prop1_ii {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn) :
    ∀ᵐ ω ∂P, ∀ x, MapClusterPt x atTop (fun n => xn n ω) → x ∈ optSet μ f X := by sorry

end SolutionQuality.SRP
