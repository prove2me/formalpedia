-- Prove2me | Theorems.Thm_RobustLP_Counterpart_symmetric_sum_tail_bound
-- name    : RobustLP.Counterpart.symmetric_sum_tail_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:27:25.425097+00:00
-- url     : https://prove2.me/theorems/3b9fb2e4-d75e-4ce2-b5ed-0eca8591fbc7
-- title:
--   Eq. (1): $\Pr\{\sum_j\eta_jp_j > \Omega\sqrt{\sum_jp_j^2}\}\le\exp\{-\Omega^2/2\}$ for independent symmetric $[-1,1]$ variables
-- statement:
--   Let $(S,\mathcal F,\mathbb P)$ be a probability space and $\eta_j$, $j$ in a finite index set, be independent real random variables, each symmetrically distributed ($\eta_j$ and $-\eta_j$ have the same law) and taking values in $[-1,1]$. Let $p_j$ be given reals. Then for every $\Omega>0$,
--   $$
--   \mathbb P\Big\{\sum_j \eta_j p_j > \Omega\sqrt{\sum_j p_j^2}\Big\} \le \exp\{-\Omega^2/2\}.
--   $$
--
--   This Hoeffding-type tail bound is the "well-known fact" used to conclude Proposition 1: applied to $\eta_j=\xi_{ij}$ and $p_j=a_{ij}z_{ij}$, it bounds the violation probability of each constraint of a solution of (RC[ε, δ, Ω]).
--
--   **Formalization Note** The event is strict, as printed. When all $p_j=0$ the event is empty. The weights are called `pc` in Lean. Symmetry is the equality of image measures `P.map (η j) = P.map (fun ω => -η j ω)`, independence is `iIndepFun η P`, and values in $[-1,1]$ are required at every outcome. The probability is `P.real`.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 419, §3.1, Eq. (1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RobustLP.Counterpart

/-- **Fact (1)** (Ben-Tal–Nemirovski 2000, §3.1, p. 419, Eq. (1)). Let `p_j` be given reals and
`η_j` independent random variables, each symmetrically distributed (the law of `η_j` equals the
law of `-η_j`) and taking values in `[-1, 1]`. Then for every `Ω > 0`,
`P(∑_j η_j p_j > Ω √(∑_j p_j²)) ≤ exp(-Ω²/2)`. -/
theorem symmetric_sum_tail_bound {ι : Type*} [Fintype ι]
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (η : ι → S → ℝ) (hmeas : ∀ j, Measurable (η j)) (hindep : iIndepFun η P)
    (hsymm : ∀ j, P.map (η j) = P.map (fun ω => -η j ω))
    (hbdd : ∀ j ω, η j ω ∈ Set.Icc (-1 : ℝ) 1)
    (pc : ι → ℝ) (Ω : ℝ) (hΩ : 0 < Ω) :
    P.real {ω | Ω * Real.sqrt (∑ j, pc j ^ 2) < ∑ j, η j ω * pc j} ≤
      Real.exp (-(Ω ^ 2 / 2)) := by sorry

end RobustLP.Counterpart
