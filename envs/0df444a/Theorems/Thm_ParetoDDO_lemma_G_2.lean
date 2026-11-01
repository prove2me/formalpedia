-- Prove2me | Theorems.Thm_ParetoDDO_lemma_G_2
-- name    : ParetoDDO.lemma_G_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:11.636309+00:00
-- url     : https://prove2.me/theorems/4b3d2ef9-4782-4e8d-85ed-849bd0ee7847
-- title:
--   Lemma G.2 — random vectors in a compact set have a probabilistic accumulation point
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $z_T$, $T\in\mathbb N$, random vectors with values in a compact set $Z\subseteq\mathbb R^n$. Then there is a deterministic $z_\infty\in Z$ with
--   $$
--   \limsup_{T\to\infty}\mathbb P\big[\|z_T-z_\infty\|<\rho\big]>0\qquad\text{for all }\rho>0.
--   $$
--
--   The sequence need not converge; $z_\infty$ is an accumulation point in probability, used to localize a competitor's prescriptor.
--
--   **Formalization Note** The `limsup` is taken in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - generalization: random vectors $z_T$ (measurable) → arbitrary maps $z_T:\Omega\to Z$, probabilities as outer measures; reason: for measurable $z_T$ the outer measure is the probability, so the source's statement is a special case
--   - encoding: $\limsup$ of probabilities in $[0,1]$ → `limsup` in $[0,\infty]$; reason: the same number; avoids the junk value of a real `limsup`
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Lemma G.2, p.50

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Lemma G.2** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.50). On a probability space, if random vectors
`z_T`, `T ∈ ℕ`, take values in a compact set `Z ⊆ ℝⁿ`, then there is a deterministic `z∞ ∈ Z` with
`limsup_T P[‖z_T − z∞‖ < ρ] > 0` for all `ρ > 0`.

**Formalization Note** Time is `T ∈ {1, 2, …}`. The `z_T` need not be measurable: probabilities
of events are outer measures, and the `limsup` is taken in `[0, ∞]`. -/
theorem lemma_G_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (Z : Set (Vec n)) (hZ : IsCompact Z) (z : ℕ → Ω → Vec n)
    (hzZ : ∀ T, 1 ≤ T → ∀ ω, z T ω ∈ Z) :
    ∃ zinf ∈ Z, ∀ ρ : ℝ, 0 < ρ → 0 < limsup (fun T => μ {ω | ‖z T ω - zinf‖ < ρ}) atTop := by sorry

end ParetoDDO
