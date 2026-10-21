-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_lemma_6
-- name    : StochLoadBal.Makespan.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:10.490978+00:00
-- url     : https://prove2.me/theorems/7ab3872f-9419-419b-9036-d6ba56798fe4
-- title:
--   Lemma 6 — every assignment with (13)–(14) for a feasible LP solution has expected makespan at most 4b + 10
-- statement:
--   Let $m\ge1$, let the sizes $X_{ij}\ge0$ be measurable and integrable with the jobs independent, let $b\ge0$, let $y$ be a feasible solution of the LP (5)–(9) with parameter $b$, and let $\sigma$ be any assignment with properties (13)–(14) (an output of the rounding). Then
--   $$\mathbb E\Big[\max_{i\in[m]}\sum_{j\in J_i}X_{ij}\Big]\ \le\ 4b+10 .$$
--
--   This is the upper-bound half of Theorem 1 at unit scale: whenever the LP is feasible, the rounding returns an assignment of expected makespan $O(b)$.
--
--   **Formalization Note** The statement covers every assignment satisfying (13)–(14), not only the one the Shmoys–Tardos algorithm returns; the bound depends only on $b$.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 12, Lemma 6 (proof pp. 12–13)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (Bounding the Makespan, p. 12): for `b ≥ 0`, a feasible LP solution `y` and any
assignment `σ` with properties (13)–(14), the expected makespan is at most `4b + 10`. -/
theorem lemma_6 {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P) (hind : iIndepFun (fun j ω i => X i j ω) P)
    (b : ℝ) (hb : 0 ≤ b) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)
    (σ : Fin n → Fin m) (hσ : IsRoundingOutput P X b y σ) :
    expMakespan P X σ ≤ 4 * b + 10 := by sorry

end StochLoadBal.Makespan
