-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_theorem_0_1
-- name    : SolomonRWRE.Recurrence.theorem_0_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:34.183977+00:00
-- url     : https://prove2.me/theorems/8e755268-0fb3-400b-afd0-975381dea137
-- title:
--   Theorem (0.1) — if M_α({X_n} ∈ S) = 1 for a.e. environment α, then P({X_n} ∈ S) = 1
-- statement:
--   Let $(X_n)$ be the random walk in the i.i.d. random environment $\alpha=(\alpha_n)_{n\in\mathbb Z}$, $Q$ the law of $\alpha$, and $M_a$ the chain in the fixed environment $a$ started at $0$. Let $S\subset\mathbb Z^{\mathbb N}$ be a measurable set of paths. If
--   $$M_a\big(\{X_n\}\in S\big)=1\quad\text{for $Q$-almost every environment } a,$$
--   then
--   $$P\big(\{X_n\}\in S\big)=1 .$$
--
--   A property that holds almost surely for the walk in almost every fixed environment therefore holds almost surely for the random walk in a random environment. This is how the fixed-environment results of Lemma (1.5) become statements about the random walk in Theorem (1.7).
--
--   **Formalization Note** "$M_a(\{X_n\}\in S)=1$" is stated as: every probability measure on path space $\mathbb Z^{\mathbb N}$ under which the coordinate process is the chain $M_a$ started at $0$ gives $S$ measure $1$. The paper's name $\Omega$ for the path set is replaced by $S$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 2, Theorem (0.1)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), p. 2,
Theorem (0.1): a property of paths that holds `M_α`-almost surely for almost every fixed
environment `α` holds almost surely for the random walk in a random environment.

**Formalization Note.** The paper's path set `Ω ⊂ Z^N` is `S` here (the name `Ω` is taken by
the sample space). "`M_α({X_n} ∈ S) = 1`" is read as: every probability measure `ν` on path
space under which the coordinate process is the chain `M_α` started at `0` gives `S` measure
`1`. "For a.e. environment" is with respect to the environment law `Q = P.map (env α)`. -/
theorem theorem_0_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (S : Set (ℕ → ℤ)) (hS : MeasurableSet S)
    (h : ∀ᵐ a ∂(P.map (env α)), ∀ ν : Measure (ℕ → ℤ), IsProbabilityMeasure ν →
      IsChainInEnv ν a 0 (fun n w => w n) → ν S = 1) :
    P {ω | (fun n => X n ω) ∈ S} = 1 := by sorry

end SolomonRWRE.Recurrence
