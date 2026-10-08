-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_chain_lower_bound
-- name    : StochSchedPrec.InForest.chain_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:12.847104+00:00
-- url     : https://prove2.me/theorems/94f4c464-5ebd-4bc7-9bf2-cff71d87b843
-- title:
--   §4, p. 798 — the critical-chain length ℓ_j(p) is a lower bound on job j's completion time
-- statement:
--   Consider acyclic precedence constraints on $V$, $m\ge1$ machines, no release dates, and independent, nonnegative, integrable processing times $P_j$. Let $\sigma$ assign to every realization $p\ge0$ a feasible schedule $\sigma(p)$, fix for every $p$ a selector of critical predecessors for $\sigma(p)$, and let $\ell_j(p)$ be the length of the resulting critical chain for $j$ (Definition 2.3). Then:
--   1. for every realization $p\ge0$, every feasible schedule $S'$ for $p$ and every job $j$,
--   $$\ell_j(p)\ \le\ S'_j+p_j ;$$
--   2. for every feasible nonanticipatory policy $\Pi$ with integrable completion times and every job $j$,
--   $$\mathrm E[\ell_j(P)]\ \le\ \mathrm E[C^\Pi_j(P)] .$$
--
--   In the proof of Theorem 4.1, which the proof of Theorem 4.5 repeats, this shows that $\sum_j w_j\mathrm E[\ell_j(P)]$ is a lower bound on the expected performance of an optimal policy.
--
--   **Formalization Note** The page states the claim for the critical chains of the algorithm's schedule; it holds for the critical chains of any feasible schedule, which is how it is stated here. $\ell_j(P)$ is assumed almost-everywhere measurable (it is a random variable on the page).
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 798, §4, proof of Theorem 4.1, paragraph "Now, for any job j and any realization p"

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_Graham
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest

theorem chain_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (hPint : ∀ j, Integrable (P j) Pr)
    (σ : (V → ℝ) → (V → ℝ)) (hσ : ∀ p, IsNonneg p → IsFeasibleSchedule A m p (σ p))
    (crit : (V → ℝ) → V → Option V) (hcrit : ∀ p, IsNonneg p → IsCritSelector A p (σ p) (crit p))
    (hℓmeas : ∀ j, AEMeasurable
      (fun ω => chainLen (crit (fun k => P k ω)) (fun k => P k ω) j) Pr) :
    (∀ p, IsNonneg p → ∀ S' : V → ℝ, IsFeasibleSchedule A m p S' →
        ∀ j, chainLen (crit p) p j ≤ S' j + p j) ∧
      ∀ pol : (V → ℝ) → (V → ℝ), IsComparator A m P Pr pol → ∀ j,
        ∫ ω, chainLen (crit (fun k => P k ω)) (fun k => P k ω) j ∂Pr ≤
          ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by sorry

end StochSchedPrec.InForest
