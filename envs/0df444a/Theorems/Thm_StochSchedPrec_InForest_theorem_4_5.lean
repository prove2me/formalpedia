-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_theorem_4_5
-- name    : StochSchedPrec.InForest.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:36.704784+00:00
-- url     : https://prove2.me/theorems/0380aed0-0b79-44cd-8f3b-ec71e5221bbf
-- title:
--   Theorem 4.5, p. 800 — Graham's list scheduling by LP order is a (2 − 1/m + max{1, (m−1)Δ/m})-approximation for P|in-forest|E[Σ w_j C_j]
-- statement:
--   Consider an instance of $P\,|\,\text{in-forest}\,|\,\mathrm E[\sum w_jC_j]$: a finite job set $V$ with acyclic in-forest precedence constraints (each job has at most one successor), $m\ge1$ identical parallel machines, no release dates, nonnegative weights $w_j$, and stochastically independent nonnegative processing times $P_j$ with $\mathrm{CV}[P_j]\le\sqrt\Delta$ for all $j$ and some $\Delta\ge0$. Let $C^{\mathrm{LP}}$ be an optimal solution of the LP-relaxation of §3 and $L$ a priority list according to $C^{\mathrm{LP}}$ (nondecreasing $C^{\mathrm{LP}}$). Let $\gamma$ be Graham's list scheduling with list $L$. Then Graham's list scheduling is an $\alpha$-approximation with
--   $$\alpha=2-\frac1m+\max\Big\{1,\frac{m-1}{m}\Delta\Big\}:$$
--   for every feasible nonanticipatory policy $\Pi$ with integrable completion times,
--   $$\mathrm E\Big[\sum_{j\in V}w_j\,C^\gamma_j(P)\Big]\ \le\ \alpha\cdot\mathrm E\Big[\sum_{j\in V}w_j\,C^\Pi_j(P)\Big].$$
--
--   For NBUE processing times ($\Delta=1$) the guarantee is $3-1/m$.
--
--   **Formalization Note** "$\alpha$-approximation" is stated against every comparator policy rather than an optimal one, which implies the page's statement and does not presuppose that an optimal policy exists. The completion times of Graham's schedule are assumed almost-everywhere measurable (§5, p. 800, asserts this for the paper's policies). The CV bound includes $\mathrm E[P_j^2]<\infty$ and $\mathrm E[P_j]>0$.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 800, Theorem 4.5

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Definitions.Def_StochSchedPrec_InForest_Graham
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest

theorem theorem_4_5 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A) (hforest : IsInForest A)
    (w : V → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (Δ : ℝ) (hCV : CVBound P Pr Δ)
    (C : V → ℝ) (hC : IsLPOptimal (fun j => ∫ ω, P j ω ∂Pr) A m Δ w C)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsSortedBy L C)
    (γ : (V → ℝ) → (V → ℝ)) (hγ : ∀ p, IsNonneg p → IsGraham A m L p (γ p))
    (hγmeas : ∀ j, AEMeasurable (fun ω => γ (fun k => P k ω) j) Pr) :
    ∀ pol : (V → ℝ) → (V → ℝ), IsComparator A m P Pr pol →
      ∫ ω, (∑ j, w j * (γ (fun k => P k ω) j + P j ω)) ∂Pr ≤
        (2 - 1 / (m : ℝ) + max 1 (((m : ℝ) - 1) / m * Δ)) *
          ∫ ω, (∑ j, w j * (pol (fun k => P k ω) j + P j ω)) ∂Pr := by sorry

end StochSchedPrec.InForest
