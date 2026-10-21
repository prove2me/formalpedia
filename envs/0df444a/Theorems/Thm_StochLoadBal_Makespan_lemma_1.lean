-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_lemma_1
-- name    : StochLoadBal.Makespan.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:07.933786+00:00
-- url     : https://prove2.me/theorems/7a884c6a-d671-4cb1-805d-25c124083584
-- title:
--   Lemma 1, with the independence it needs — exceptional items lower bound E[max_j X_j] ≥ L/2
-- statement:
--   Let $L>0$ and let $X_1,\dots,X_t$ ($t\ge1$) be independent, integrable random variables, each taking either the value $0$ or a value at least $L$. If
--   $$\sum_{j=1}^t \mathbb E[X_j]\ \ge\ L,$$
--   then
--   $$\mathbb E\Big[\max_{j} X_j\Big]\ \ge\ \frac L2 .$$
--
--   This is the lower bound the paper uses for exceptional parts: applied with $L=1$ to the exceptional parts of the jobs of an assignment, it shows that a large total expected exceptional size forces a large expected makespan (inequality (3) of Lemma 5).
--
--   **Formalization Note** The page states the lemma for "non-negative discrete random variables" without saying "independent"; independence is necessary (for $t$ copies of $L\cdot\mathbf 1_A$ with $P(A)=1/t$ one has $\sum_j\mathbb E[X_j]=L$ but $\mathbb E[\max_j X_j]=L/t$) and is what the cited source and the application in Lemma 5 have, so it is a hypothesis here. "Discrete" is dropped: the statement holds for all such independent variables. Integrability keeps the Bochner integrals honest.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 5, Lemma 1 (proof p. 6)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (Exceptional Items Lower Bound, p. 5), with the independence it needs and without
"discrete": if `X_1, …, X_t` are independent, integrable, and each takes the value `0` or a value
`≥ L > 0`, and `Σ_j E[X_j] ≥ L`, then `E[max_j X_j] ≥ L / 2`. -/
theorem lemma_1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (t : ℕ) (ht : 1 ≤ t) (L : ℝ) (hL : 0 < L) (X : Fin t → Ω → ℝ)
    (hmeas : ∀ j, Measurable (X j)) (hint : ∀ j, Integrable (X j) P)
    (hind : iIndepFun X P)
    (hval : ∀ j ω, X j ω = 0 ∨ L ≤ X j ω)
    (hsum : L ≤ ∑ j, ∫ ω, X j ω ∂P) :
    L / 2 ≤ ∫ ω, (⨆ j, X j ω) ∂P := by sorry

end StochLoadBal.Makespan
