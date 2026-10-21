-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_lemma_7
-- name    : StochLoadBal.Makespan.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:07.460694+00:00
-- url     : https://prove2.me/theorems/df8d2a1c-f7f0-4d3b-b523-6419f752928d
-- title:
--   Lemma 7 — Pr[max_{i∈I^hi} T_i > b + 1 + α] ≤ 2^(2−α)/(α − 2) for α > 2
-- statement:
--   Under the hypotheses of Observation 3 (sizes $X_{ij}\ge0$ measurable, integrable, jobs independent; $y$ feasible for the LP (5)–(9) with parameter $b$; $\sigma$ an assignment with (13)–(14)), let $I^{hi}$ be the set of machines of class at least $3$ and $T_i=\sum_{j\in J_i}X'_{ij}$ the truncated load of machine $i$. Then for every $\alpha>2$,
--   $$\Pr\Big[\max_{i\in I^{hi}}T_i\ >\ b+1+\alpha\Big]\ \le\ \frac{2^{2-\alpha}}{\alpha-2}.$$
--
--   Integrating this tail bound gives $\mathbb E[\max_{i\in I^{hi}}T_i]\le b+5$, the first term of the bound $4b+10$ in Lemma 6.
--
--   **Formalization Note** The event is written as "some machine of class at least $3$ has $T_i>b+1+\alpha$", which is the event $\max_{i\in I^{hi}}T_i>b+1+\alpha$ and is empty when $I^{hi}=\emptyset$.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 13, Lemma 7 (I^hi and T_i defined in the proof of Lemma 6, p. 12)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Lemma 7 (p. 13): for a feasible LP solution `y`, an assignment `σ` with (13)–(14), and
`α > 2`, the probability that some machine `i ∈ I^hi` (class `≥ 3`) has truncated load
`T_i = Σ_{j ∈ J_i} X'_{ij} > b + 1 + α` is at most `2^{2-α}/(α - 2)`. -/
theorem lemma_7 {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P) (hind : iIndepFun (fun j ω i => X i j ω) P)
    (b : ℝ) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)
    (σ : Fin n → Fin m) (hσ : IsRoundingOutput P X b y σ) (α : ℝ) (hα : 2 < α) :
    (P {ω | ∃ i, 3 ≤ machineClass P X b y i ∧
        b + 1 + α < ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)}).toReal
      ≤ (2 : ℝ) ^ (2 - α) / (α - 2) := by sorry

end StochLoadBal.Makespan
